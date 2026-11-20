import Miri.Interpreter.TimeShims
import Miri.Interpreter.ChronoTzData

/-! Pure calendar/timezone portion of the chrono 0.4 / chrono-tz 0.10
UTC-to-local path used by Miri's `localtime_r`. Transition records are the
generated IANA 2025b tables in `ChronoTzData`; this module never consults host
zoneinfo or imports the Input layer. -/
namespace Miri.Interpreter.ChronoTz
open Miri.ABI Miri.Memory

abbrev TZ := String
abbrev Timestamp := Int64

private def splitPair (separator value : String) : Option (String × String) :=
  match value.splitOn separator with
  | [left,right] => some (left,right)
  | _ => none

private def timezoneName (input : String) : Option String := Id.run do
  for row in Miri.Interpreter.ChronoTzData.aliases.splitOn "\n" do
    match splitPair "|" row with
    | some (name,canonical) => if name == input then return some canonical
    | none => pure ()
  return none

private structure ZoneTable where
  initialOffset : Int
  transitions : Array (Int × Int)

private def parseZone (name : String) : Option ZoneTable := Id.run do
  let mut rowFound : Option String := none
  for row in Miri.Interpreter.ChronoTzData.zones.splitOn "\n" do
    if row.startsWith (name ++ "|") then
      rowFound := some row
      break
  let some row := rowFound | return none
  let fields := row.splitOn "|"
  let [_,initialText,pointsText] := fields | return none
  let some initialOffset := initialText.toInt? | return none
  let mut transitions := #[]
  if !pointsText.isEmpty then
    for point in pointsText.splitOn "," do
      let some (timeText,offsetText) := splitPair ":" point | return none
      let some transitionTime := timeText.toInt? | return none
      let some offset := offsetText.toInt? | return none
      transitions := transitions.push (transitionTime,offset)
  return some ⟨initialOffset,transitions⟩

/-- `DateTime::from_timestamp(secs, 0)` converts to CE days and then uses
`NaiveDate::from_num_days_from_ce_opt`; mirror its real MIN_YEAR/MAX_YEAR
bounds rather than accepting every i32 day count. -/
def validTimestamp (seconds : Int64) : Bool := Id.run do
  let days := seconds.toInt / 86400
  let ceDay := days + 719163
  /- Chrono NaiveDate uses these tighter year bounds so its internal encoded
  year/ordinal representation retains headroom for timezone offset arithmetic.
  These are the CE day numbers of NaiveDate::MIN (MIN_YEAR-01-01) and
  NaiveDate::MAX (MAX_YEAR-12-31) in chrono 0.4.45. -/
  return (-95746129 : Int) ≤ ceDay && ceDay ≤ 95745399

private def utcOffset (table : ZoneTable) (seconds : Int) : Int := Id.run do
  let mut low := 0
  let mut high := table.transitions.size
  while low < high do
    let middle := (low + high) / 2
    match table.transitions[middle]? with
    | none => high := middle
    | some (transitionTime,_) =>
      if transitionTime ≤ seconds then low := middle + 1 else high := middle
  if low == 0 then return table.initialOffset
  match table.transitions[low - 1]? with
  | some (_,offset) => return offset
  | none => return table.initialOffset

private def isLeapYear (year : Int) : Bool :=
  year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)

private def monthLength (year month : Int) : Int :=
  if month == 2 then if isLeapYear year then 29 else 28
  else if #[4,6,9,11].contains month then 30 else 31

/-- Gregorian calendar conversion using chrono's proleptic Gregorian calendar.
The input day is a Euclidean count relative to 1970-01-01. -/
private def civilFromDays (days : Int) : Int × Int × Int := Id.run do
  let shifted := days + 719468
  let era := shifted / 146097
  let dayOfEra := shifted - era * 146097
  let yearOfEra := (dayOfEra - dayOfEra / 1460 + dayOfEra / 36524 - dayOfEra / 146096) / 365
  let mut year := yearOfEra + era * 400
  let dayOfYear := dayOfEra - (365 * yearOfEra + yearOfEra / 4 - yearOfEra / 100)
  let monthPrime := (5 * dayOfYear + 2) / 153
  let day := dayOfYear - (153 * monthPrime + 2) / 5 + 1
  let month := monthPrime + (if monthPrime < 10 then 3 else -9)
  if month ≤ 2 then year := year + 1
  return (year,month,day)

private def ordinal (year month day : Int) : Int := Id.run do
  let mut result := day - 1
  let mut current := 1
  while current < month do
    result := result + monthLength year current
    current := current + 1
  return result

private def brokenDown (localSeconds offset : Int) : TimeShims.BrokenDown := Id.run do
  let days := localSeconds / 86400
  let daySeconds := localSeconds % 86400
  let (year,month,day) := civilFromDays days
  let hour := daySeconds / 3600
  let minute := daySeconds % 3600 / 60
  let second := daySeconds % 60
  let weekday := (days + 4) % 7
  return {
    second := second.toNat
    minute := minute.toNat
    hour := hour.toNat
    day := day.toNat
    month0 := (month - 1).toNat
    weekdaySunday := weekday.toNat
    ordinal0 := (ordinal year month day).toNat
    year := Int32.ofInt year
    offsetSeconds := Int32.ofInt offset }

def timestamp (seconds : Int64) : Option Timestamp :=
  if validTimestamp seconds then some seconds else none

def timezone (input : String) : Option TZ := timezoneName input

def convert (value : Timestamp) (zone : TZ) : Option TimeShims.BrokenDown := do
  let table ← parseZone zone
  let seconds := value.toInt
  let offset := utcOffset table seconds
  pure (brokenDown (seconds + offset) offset)

end Miri.Interpreter.ChronoTz
