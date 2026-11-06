module
public import Adapter

@[expose] public section
namespace BoundConsumer
open CheckedByteLeaf

inductive Target where | a64 | x64 deriving DecidableEq, Repr
inductive Model where | kraken8af7806 | other deriving DecidableEq, Repr
inductive Claim where | readByteFullFrame | resultOnly deriving DecidableEq, Repr

structure Request where
  image : List UInt8
  entry : Nat
  pc : Int64
  target : Target
  model : Model
  claim : Claim

def Supported (r : Request) : Prop :=
  r.target = .a64 ∧ r.model = .kraken8af7806 ∧ r.claim = .readByteFullFrame
instance (r : Request) : Decidable (Supported r) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Only data: no expressions, proof references, callbacks or imported declarations. -/
structure Fields where
  entry : Nat
  pc : Nat
  deriving DecidableEq, Repr

def header : List UInt8 := [0x4b,0x52,0x43,1,1,1,1]
def serialize (f : Fields) : List UInt8 := header ++ Nat.toBytes 4 f.entry ++ Nat.toBytes 8 f.pc
def entryBytes (raw : List UInt8) : List UInt8 := (raw.drop 7).take 4
def pcBytes (raw : List UInt8) : List UInt8 := raw.drop 11

def parseRaw (raw : List UInt8) : Option Fields :=
  if raw.length = 19 ∧ raw.take 7 = header ∧ Nat.ofBytes (pcBytes raw) < 2^63 then
    some ⟨Nat.ofBytes (entryBytes raw), Nat.ofBytes (pcBytes raw)⟩
  else none

theorem bytes_bound (bs : List UInt8) : Nat.ofBytes bs < 256^bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    have hb := b.toNat_lt
    simp only [Nat.ofBytes_cons, List.length_cons, Nat.pow_succ]
    omega

theorem serialize_length (f : Fields) : (serialize f).length = 19 := by
  simp [serialize, header, Nat.toBytes_length]

theorem serialized_parts (f : Fields) :
    (serialize f).take 7 = header ∧ entryBytes (serialize f) = Nat.toBytes 4 f.entry ∧
      pcBytes (serialize f) = Nat.toBytes 8 f.pc := by
  simp [serialize, header, entryBytes, pcBytes, Nat.toBytes_length,
    List.take_append, List.drop_append]

theorem roundtrip (f : Fields) (he : f.entry < 2^32) (hp : f.pc < 2^63) :
    parseRaw (serialize f) = some f := by
  have hp64 : f.pc < 2^64 := by omega
  simp [parseRaw, serialize_length, (serialized_parts f).1,
    (serialized_parts f).2.1, (serialized_parts f).2.2,
    Nat.ofBytes_toBytes, Nat.take, Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt hp64, hp]

theorem parse_sound (raw : List UInt8) (f : Fields) (h : parseRaw raw = some f) :
    raw = serialize f ∧ f.entry < 2^32 ∧ f.pc < 2^63 := by
  unfold parseRaw at h
  split at h
  next hp =>
    rcases hp with ⟨hl,hh,hpc⟩
    have hf := Option.some.inj h
    subst f
    have he_len : (entryBytes raw).length = 4 := by simp [entryBytes, hl]
    have hp_len : (pcBytes raw).length = 8 := by simp [pcBytes, hl]
    have he_bound := bytes_bound (entryBytes raw)
    rw [he_len] at he_bound
    have he_inverse : Nat.toBytes 4 (Nat.ofBytes (entryBytes raw)) = entryBytes raw := by
      simpa only [List.take_of_length_le (by omega : (entryBytes raw).length ≤ 4)] using
        Nat.toBytes_ofBytes 4 (entryBytes raw) (by omega)
    have hp_inverse : Nat.toBytes 8 (Nat.ofBytes (pcBytes raw)) = pcBytes raw := by
      simpa only [List.take_of_length_le (by omega : (pcBytes raw).length ≤ 8)] using
        Nat.toBytes_ofBytes 8 (pcBytes raw) (by omega)
    refine ⟨?_, he_bound, hpc⟩
    simp only [serialize, he_inverse, hp_inverse]
    rw [← hh]
    have hsplit := List.take_append_drop 4 (raw.drop 7)
    calc
      raw = raw.take 7 ++ raw.drop 7 := (List.take_append_drop 7 raw).symm
      _ = raw.take 7 ++ (entryBytes raw ++ pcBytes raw) := by
        congr 1
        simpa [entryBytes, pcBytes, List.drop_drop] using hsplit.symm
      _ = raw.take 7 ++ entryBytes raw ++ pcBytes raw := (List.append_assoc _ _ _).symm
  next => cases h

theorem parse_iff (raw : List UInt8) (f : Fields) :
    parseRaw raw = some f ↔ raw = serialize f ∧ f.entry < 2^32 ∧ f.pc < 2^63 := by
  constructor
  · exact parse_sound raw f
  · rintro ⟨rfl,he,hp⟩
    exact roundtrip f he hp

def slice (image : List UInt8) (entry : Nat) : List UInt8 := (image.drop entry).take 8

/-- The consumer selects the complete request. The producer supplies data only. -/
def check (r : Request) (candidate raw : List UInt8) : Option Executable := do
  let f ← parseRaw raw
  if candidate = r.image ∧ Supported r ∧ f.entry = r.entry ∧
      f.pc = r.pc.toInt.toNat ∧ r.entry + 8 ≤ candidate.length then
    certificate r.pc (slice candidate r.entry)
  else none

def accepted (r : Request) (candidate raw : List UInt8) : Bool := (check r candidate raw).isSome

theorem check_binding (r : Request) (candidate raw : List UInt8) (e : Executable)
    (h : check r candidate raw = some e) :
    candidate = r.image ∧ Supported r ∧ r.entry + 8 ≤ r.image.length ∧
    LayoutOK r.pc ∧ slice candidate r.entry = canonicalBytes ∧ e = executable r.pc 0 ∧
    ∃ f : Fields, raw = serialize f ∧ f.entry = r.entry ∧ f.pc = r.pc.toInt.toNat ∧
      f.entry < 2^32 ∧ f.pc < 2^63 := by
  unfold check at h
  cases hp : parseRaw raw with
  | none => simp [hp] at h
  | some f =>
    simp only [hp] at h
    dsimp only [Bind.bind, Option.bind] at h
    split at h
    next hc =>
      rcases hc with ⟨hi,hs,he,hpc,hspan⟩
      rcases (certificate_iff _ _ _).mp h with ⟨hl,hbytes,hexe⟩
      rcases parse_sound raw f hp with ⟨hraw,hentry,hpcbound⟩
      exact ⟨hi,hs,by simpa only [hi] using hspan,hl,hbytes,hexe,
        f,hraw,he,hpc,hentry,hpcbound⟩
    next => cases h

def FullPost (_r : Request) (d : MachineData) (v : UInt8) (base : BitVec 64)
    (R : DataMem → Prop) (s : MachineState) : Prop :=
  s.data = resultData d v.toBitVec ∧ s.pc = Int64.ofBitVec d.regs.X30.toBitVec ∧
    s.data.dmem = d.dmem ∧ s.data.dmem =⋆ Eq (v.At base) ⋆ R

/-- Fixed consumer meaning. Logical memory/authority premises are not certificate fields. -/
def Meaning (r : Request) (e : Executable) : Prop :=
  Supported r ∧ ∀ (d : MachineData) (v : UInt8) (base : BitVec 64) (R : DataMem → Prop)
    (exec : Std.Rco Int64 → Prop),
    d.regs.X0.toBitVec = base → (d.dmem =⋆ Eq (v.At base) ⋆ R) →
    exec ⟨r.pc,r.pc+4⟩ → exec ⟨r.pc+4,r.pc+4+4⟩ →
    PermissionAll (withinRegion base.toNat 1) (fun _ _ => False) exec (FullPost r d v base R)
      (Executable.straightline e ⟨d,r.pc⟩ .done) ∧
    observe (Executable.straightline e ⟨d,r.pc⟩ .done) =
      some (exactTrace r.pc d,⟨resultData d v.toBitVec,Int64.ofBitVec d.regs.X30.toBitVec⟩) ∧
    Executable.step e ⟨d,r.pc⟩ .done =
      .require_exec_access ⟨r.pc,r.pc+4⟩ (fun _ =>
        .require_read_access d.regs.X0.toBitVec .W8 (fun _ => .done ⟨resultData d v.toBitVec,r.pc+4⟩)) ∧
    Executable.step e ⟨resultData d v.toBitVec,r.pc+4⟩ .done =
      .require_exec_access ⟨r.pc+4,r.pc+4+4⟩ (fun _ =>
        .done ⟨resultData d v.toBitVec,Int64.ofBitVec d.regs.X30.toBitVec⟩) ∧
    (r.pc+4).toInt = r.pc.toInt+4 ∧ (r.pc+4+4).toInt = r.pc.toInt+8

theorem consumer_sound (r : Request) (candidate raw : List UInt8) (e : Executable)
    (h : check r candidate raw = some e) : Meaning r e := by
  rcases check_binding r candidate raw e h with ⟨_,hs,_,hl,_,he,_⟩
  refine ⟨hs, ?_⟩
  intro d v base R exec harg hsep hx0 hx1
  have hload := resource_load d v R (by simpa only [harg] using hsep)
  have hcert : certificate r.pc (slice candidate r.entry) = some e :=
    (certificate_iff _ _ _).mpr ⟨hl,(check_binding r candidate raw e h).2.2.2.2.1,he⟩
  have hpermission := checked_resource_contract r.pc (slice candidate r.entry) e hcert
    d v base harg R hsep exec hx0 hx1
  subst e
  refine ⟨hpermission, complete_trace r.pc d v.toBitVec hload,
    actual_load_step r.pc hl d v.toBitVec hload, ?_, (layout_endpoints r.pc hl).1,
    (layout_endpoints r.pc hl).2⟩
  simpa only [resultData] using actual_ret_step r.pc hl (resultData d v.toBitVec)

theorem accepted_sound (r : Request) (candidate raw : List UInt8)
    (h : accepted r candidate raw = true) : ∃ e, check r candidate raw = some e ∧ Meaning r e := by
  unfold accepted at h
  cases hc : check r candidate raw with
  | none => simp [hc] at h
  | some e => exact ⟨e,rfl,consumer_sound r candidate raw e hc⟩

theorem closed_grammar (r : Request) (candidate raw : List UInt8) (e : Executable)
    (h : check r candidate raw = some e) :
    raw.length = 19 ∧ raw.take 7 = header ∧
    ∃ f : Fields, raw = serialize f ∧ f.entry < 2^32 ∧ f.pc < 2^63 := by
  rcases (check_binding r candidate raw e h).2.2.2.2.2.2 with ⟨f,hr,_,_,he,hpc⟩
  subst raw
  exact ⟨serialize_length f,(serialized_parts f).1,f,rfl,he,hpc⟩

theorem wrong_image_rejected (r : Request) (candidate raw : List UInt8)
    (h : candidate ≠ r.image) : check r candidate raw = none := by
  cases hc : check r candidate raw with
  | none => rfl
  | some e => exact False.elim (h (check_binding r candidate raw e hc).1)

theorem wrong_length_rejected (raw : List UInt8) (h : raw.length ≠ 19) : parseRaw raw = none := by
  simp [parseRaw,h]

theorem bad_header_rejected (raw : List UInt8) (h : raw.take 7 ≠ header) : parseRaw raw = none := by
  simp [parseRaw,h]

theorem parse_rejection_rejects (r : Request) (candidate raw : List UInt8)
    (h : parseRaw raw = none) : check r candidate raw = none := by simp [check,h]

theorem trailing_rejected (r : Request) (candidate : List UInt8) (f : Fields) (byte : UInt8) :
    check r candidate (serialize f ++ [byte]) = none := by
  apply parse_rejection_rejects
  apply wrong_length_rejected
  simp [serialize_length]

theorem unsupported_request_rejected (r : Request) (candidate raw : List UInt8)
    (h : ¬ Supported r) : check r candidate raw = none := by
  cases hc : check r candidate raw with
  | none => rfl
  | some e => exact False.elim (h (check_binding r candidate raw e hc).2.1)

theorem wrong_entry_rejected (r : Request) (candidate raw : List UInt8) (f : Fields)
    (hp : parseRaw raw = some f) (h : f.entry ≠ r.entry) : check r candidate raw = none := by
  simp [check,hp,h]

theorem wrong_pc_rejected (r : Request) (candidate raw : List UInt8) (f : Fields)
    (hp : parseRaw raw = some f) (h : f.pc ≠ r.pc.toInt.toNat) : check r candidate raw = none := by
  unfold check
  rw [hp]
  dsimp only [Bind.bind,Option.bind]
  split
  next hc => exact False.elim (h hc.2.2.2.1)
  next => rfl

theorem accepted_empty_span_rejected (r : Request) (candidate raw : List UInt8) (e : Executable)
    (h : check r candidate raw = some e) (d : MachineData) (v : UInt8)
    (base : BitVec 64) (harg : d.regs.X0.toBitVec = base) (R : DataMem → Prop)
    (hsep : d.dmem =⋆ Eq (v.At base) ⋆ R) (exec : Std.Rco Int64 → Prop)
    (post : MachineState → Prop) :
    ¬ PermissionAll (withinRegion base.toNat 0) (fun _ _ => False) exec post
      (Executable.straightline e ⟨d,r.pc⟩ .done) := by
  rcases check_binding r candidate raw e h with ⟨_,_,_,_,_,he,_⟩
  have hload := resource_load d v R (by simpa only [harg] using hsep)
  subst e
  simpa only [← harg,UInt64.toNat_toBitVec] using
    empty_span_rejected r.pc d v.toBitVec hload (fun _ _ => False) exec post

theorem accepted_wrong_return_rejected (r : Request) (candidate raw : List UInt8) (e : Executable)
    (h : check r candidate raw = some e) (d : MachineData) (v : UInt8)
    (R : DataMem → Prop) (hsep : d.dmem =⋆ Eq (v.At d.regs.X0.toBitVec) ⋆ R)
    (wrong : Int64) (hne : Int64.ofBitVec d.regs.X30.toBitVec ≠ wrong) :
    ¬ (Executable.straightline e ⟨d,r.pc⟩ .done).All (fun s => s.pc = wrong) := by
  rcases check_binding r candidate raw e h with ⟨_,_,_,_,_,he,_⟩
  subst e
  exact wrong_return_rejected r.pc d v.toBitVec (resource_load d v R hsep) wrong hne

theorem accepted_wrong_frame_rejected (r : Request) (candidate raw : List UInt8) (e : Executable)
    (h : check r candidate raw = some e) (d : MachineData) (v : UInt8)
    (R : DataMem → Prop) (hsep : d.dmem =⋆ Eq (v.At d.regs.X0.toBitVec) ⋆ R)
    (wrong : UInt64) (hne : d.regs.X19 ≠ wrong) :
    ¬ (Executable.straightline e ⟨d,r.pc⟩ .done).All (fun s => s.data.regs.X19 = wrong) := by
  rcases check_binding r candidate raw e h with ⟨_,_,_,_,_,he,_⟩
  subst e
  exact wrong_frame_rejected r.pc d v.toBitVec (resource_load d v R hsep) wrong hne

def ownedImage : List UInt8 := [0,0,64,57,192,3,95,214]
def fixedRequest : Request := ⟨ownedImage,0,4096,.a64,.kraken8af7806,.readByteFullFrame⟩
def goodFields : Fields := ⟨0,4096⟩
def goodRaw : List UInt8 := serialize goodFields

theorem concrete_accept : check fixedRequest ownedImage goodRaw = some (executable 4096 0) := by rfl
theorem concrete_meaning : Meaning fixedRequest (executable 4096 0) :=
  consumer_sound fixedRequest ownedImage goodRaw _ concrete_accept

theorem changed_byte_zero_rejected : check fixedRequest [1,0,64,57,192,3,95,214] goodRaw = none := by rfl
theorem hidden_image_tail_rejected : check fixedRequest (ownedImage ++ [0]) goodRaw = none := by rfl
theorem missing_input_rejected : check fixedRequest ownedImage (goodRaw.take 18) = none := by rfl
theorem trailing_input_rejected : check fixedRequest ownedImage (goodRaw ++ [0]) = none := by rfl
theorem changed_entry_rejected : check fixedRequest ownedImage (serialize ⟨1,4096⟩) = none := by rfl
theorem changed_pc_rejected : check fixedRequest ownedImage (serialize ⟨0,4100⟩) = none := by rfl
theorem changed_target_tag_rejected : check fixedRequest ownedImage (goodRaw.set 4 2) = none := by rfl
theorem changed_model_tag_rejected : check fixedRequest ownedImage (goodRaw.set 5 2) = none := by rfl
theorem changed_claim_tag_rejected : check fixedRequest ownedImage (goodRaw.set 6 2) = none := by rfl
theorem wrong_version_rejected : check fixedRequest ownedImage (goodRaw.set 3 2) = none := by rfl
theorem pc_topbit_rejected : parseRaw (serialize ⟨0,2^63⟩) = none := by rfl
theorem wrong_request_target_rejected : check {fixedRequest with target := .x64} ownedImage goodRaw = none := by rfl
theorem wrong_request_model_rejected : check {fixedRequest with model := .other} ownedImage goodRaw = none := by rfl
theorem weaker_request_rejected : check {fixedRequest with claim := .resultOnly} ownedImage goodRaw = none := by rfl

#print axioms bytes_bound
#print axioms serialize_length
#print axioms serialized_parts
#print axioms roundtrip
#print axioms parse_sound
#print axioms parse_iff
#print axioms check_binding
#print axioms consumer_sound
#print axioms accepted_sound
#print axioms closed_grammar
#print axioms wrong_image_rejected
#print axioms wrong_length_rejected
#print axioms bad_header_rejected
#print axioms parse_rejection_rejects
#print axioms trailing_rejected
#print axioms unsupported_request_rejected
#print axioms wrong_entry_rejected
#print axioms wrong_pc_rejected
#print axioms accepted_empty_span_rejected
#print axioms accepted_wrong_return_rejected
#print axioms accepted_wrong_frame_rejected
#print axioms concrete_accept
#print axioms concrete_meaning
#print axioms changed_byte_zero_rejected
#print axioms hidden_image_tail_rejected
#print axioms missing_input_rejected
#print axioms trailing_input_rejected
#print axioms changed_entry_rejected
#print axioms changed_pc_rejected
#print axioms changed_target_tag_rejected
#print axioms changed_model_tag_rejected
#print axioms changed_claim_tag_rejected
#print axioms wrong_version_rejected
#print axioms pc_topbit_rejected
#print axioms wrong_request_target_rejected
#print axioms wrong_request_model_rejected
#print axioms weaker_request_rejected

end BoundConsumer
