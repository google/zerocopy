use crate::utils::dedup::*;
use derive_generic_visitor::{ControlFlow, Drive, DriveMut, DriveTwo, Visit, VisitMut, VisitTwo};
use serde::{Deserialize, Serialize};
use serde_state::{DeserializeState, SerializeState};
use std::collections::HashMap;
use std::sync::{LazyLock, Mutex};
use std::{borrow::Cow, cmp::Ordering, ops::Range, path::PathBuf};

generate_index_type!(FileId);

/// A filename.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(Serialize, Deserialize, Drive, DriveMut, DriveTwo)]
pub enum FileName {
    /// A remapped path (namely paths into stdlib)
    Virtual(PathBuf),
    /// A local path (a file coming from the current crate for instance)
    Local(PathBuf),
    /// A "not real" file name (macro, query, etc.)
    NotReal(String),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(Serialize, Deserialize, Drive, DriveMut, DriveTwo)]
pub struct File {
    /// The file identifier.
    #[cfg_attr(feature = "charon_on_charon", charon::opaque)]
    pub id: FileId,
    /// The path to the file.
    pub name: FileName,
    /// Name of the crate this file comes from.
    pub crate_name: String,
    /// The contents of the source file, as seen by rustc at the time of translation.
    /// Some files don't have contents.
    pub contents: Option<String>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(Serialize, Deserialize, Drive, DriveMut, DriveTwo)]
pub struct Loc {
    /// The (1-based) line number.
    pub line: u32,
    /// The (0-based) column offset.
    pub col: u32,
}

/// A snippet of source code within a file.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[derive(Serialize, Deserialize, Drive, DriveMut, DriveTwo)]
pub struct SpanData {
    #[cfg_attr(feature = "charon_on_charon", charon::rename("file"))]
    pub file_id: FileId,
    #[cfg_attr(feature = "charon_on_charon", charon::rename("beg_loc"))]
    pub beg: Loc,
    #[cfg_attr(feature = "charon_on_charon", charon::rename("end_loc"))]
    pub end: Loc,
}

/// A snippet of source code within a file, along with the place the code was generated from in
/// case of macro expansion. This is a pair of the span itself (`data`) and an optional
/// "generated from" span (`generated_from_span`).
///
/// For code coming from a macro expansion, `data` is the span of the macro before expansion, i.e.
/// the location where the user wrote the call to the macro, and `generated_from_span` is where
/// the code actually comes from.
///
/// Ex:
/// ```text
/// // Below, we consider the spans for the statements inside `test`
///
/// //   the statement we consider, which gets inlined in `test`
///                          VV
/// macro_rules! macro { ... st ... } // `generated_from_span` refers to this location
///
/// fn test() {
///     macro!(); // <-- `data` refers to this location
/// }
/// ```
// A `Span` is stored inline in most AST nodes, so we care about its size. Instead of storing the
// two `SpanData`s, we pack the common case into 8 bytes:
// ```text
//     63     62..47     47..27      27..17    17..10     10..0
//   +------+----------+-----------+---------+----------+---------+
//   | wide | file(16) | beg.line  | beg.col | nb lines | end.col |
//   +------+----------+-----------+---------+----------+---------+
// ```
// The spans that don't fit this layout -- because they come from a macro expansion, span many
// lines, or point into a very large file or a very long line -- are stored in `WIDE_SPANS` and
// referred to by index.
// Some numbers to back this up:
// - For serde 1.0.228, out of 246K spans, 12 didn't fit
// - For regex 1.11.1, out of 136K spans, 25 didn't fit
// - For syn 2.0.104, out of 800K spans, 36 didn't fit
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Span(u64);

/// Bit layout of the packed representation of [`Span`].
mod pack {
    /// Set when the rest of the bits is an index into `WIDE_SPANS` instead of a packed span.
    pub const WIDE_FLAG: u64 = 1 << 63;
    pub const FILE_BITS: u32 = 16;
    pub const LINE_BITS: u32 = 20;
    pub const COL_BITS: u32 = 10;
    pub const NLINES_BITS: u32 = 7;

    pub const END_COL_SHIFT: u32 = 0;
    pub const NLINES_SHIFT: u32 = END_COL_SHIFT + COL_BITS;
    pub const BEG_COL_SHIFT: u32 = NLINES_SHIFT + NLINES_BITS;
    pub const BEG_LINE_SHIFT: u32 = BEG_COL_SHIFT + COL_BITS;
    pub const FILE_SHIFT: u32 = BEG_LINE_SHIFT + LINE_BITS;

    /// Extract the `bits` bits of `x` starting at `shift`.
    #[inline]
    pub fn get(x: u64, shift: u32, bits: u32) -> u32 {
        ((x >> shift) & ((1 << bits) - 1)) as u32
    }

    /// Put `x` in its place, if it fits in `bits` bits.
    #[inline]
    pub fn put(x: u32, shift: u32, bits: u32) -> Option<u64> {
        (u64::from(x) < (1 << bits)).then_some(u64::from(x) << shift)
    }
}

/// A [`Span`] with its contents laid out, used for serialization and unpacking into a
/// more readable format.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(
    Serialize,
    Deserialize,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo
)]
#[cfg_attr(feature = "charon_on_charon", charon::rename("Span"))]
#[serde_state(stateless)]
pub struct SerializedSpan {
    /// The source code span; for code coming from a macro expansion, the location of the macro
    /// call.
    pub data: SpanData,
    /// Where the code actually comes from, in case of macro expansion/inlining/etc.
    pub generated_from_span: Option<SpanData>,
}

/// The spans that don't fit the packed representation of [`Span`]. We store them here once and
/// refer to them by index. Entries are deduplicated so equal spans have equal representations.
///
/// This table is global and never shrinks. In practice this is fine; for instance, syn 2.0.104
/// only had distinct 36 spans here.
static WIDE_SPANS: LazyLock<Mutex<WideSpans>> = LazyLock::new(Default::default);

#[derive(Default)]
struct WideSpans {
    spans: Vec<SerializedSpan>,
    indices: HashMap<SerializedSpan, u64>,
}

impl Span {
    #[inline]
    pub fn new(data: SpanData, generated_from_span: Option<SpanData>) -> Self {
        Self::from_unpacked(SerializedSpan {
            data,
            generated_from_span,
        })
    }

    /// The source code span; for code coming from a macro expansion, the location of the macro
    /// call.
    #[inline]
    pub fn data(self) -> SpanData {
        self.unpack().data
    }

    /// Where the code actually comes from, in case of macro expansion/inlining/etc.
    #[inline]
    pub fn generated_from_span(self) -> Option<SpanData> {
        self.unpack().generated_from_span
    }

    fn from_unpacked(span: SerializedSpan) -> Self {
        match Self::pack(span) {
            Some(packed) => packed,
            None => Self::store_wide(span),
        }
    }

    fn pack(span: SerializedSpan) -> Option<Self> {
        use pack::*;
        if span.generated_from_span.is_some() {
            return None;
        }
        let data = span.data;
        let nb_lines = data.end.line.checked_sub(data.beg.line)?;
        let bits = put(data.file_id.index() as u32, FILE_SHIFT, FILE_BITS)?
            | put(data.beg.line, BEG_LINE_SHIFT, LINE_BITS)?
            | put(data.beg.col, BEG_COL_SHIFT, COL_BITS)?
            | put(nb_lines, NLINES_SHIFT, NLINES_BITS)?
            | put(data.end.col, END_COL_SHIFT, COL_BITS)?;
        Some(Span(bits))
    }

    fn unpack(self) -> SerializedSpan {
        use pack::*;
        if self.0 & WIDE_FLAG != 0 {
            return WIDE_SPANS.lock().unwrap().spans[(self.0 ^ WIDE_FLAG) as usize];
        }
        let beg_line = get(self.0, BEG_LINE_SHIFT, LINE_BITS);
        let data = SpanData {
            file_id: FileId::from_raw(get(self.0, FILE_SHIFT, FILE_BITS)),
            beg: Loc {
                line: beg_line,
                col: get(self.0, BEG_COL_SHIFT, COL_BITS),
            },
            end: Loc {
                line: beg_line + get(self.0, NLINES_SHIFT, NLINES_BITS),
                col: get(self.0, END_COL_SHIFT, COL_BITS),
            },
        };
        SerializedSpan {
            data,
            generated_from_span: None,
        }
    }

    #[cold]
    fn store_wide(span: SerializedSpan) -> Self {
        let mut wide_spans = WIDE_SPANS.lock().unwrap();
        let index = match wide_spans.indices.get(&span) {
            Some(index) => *index,
            None => {
                let index = wide_spans.spans.len() as u64;
                assert!(index & pack::WIDE_FLAG == 0, "too many wide spans");
                wide_spans.spans.push(span);
                wide_spans.indices.insert(span, index);
                index
            }
        };
        Span(index | pack::WIDE_FLAG)
    }
}

impl Ord for Span {
    fn cmp(&self, other: &Self) -> Ordering {
        if (self.0 | other.0) & pack::WIDE_FLAG == 0 {
            // Both spans are packed: the bit layout is such that comparing the packed values is
            // the same as comparing `(file, beg, end)`, so take the fast path.
            self.0.cmp(&other.0)
        } else {
            self.unpack().cmp(&other.unpack())
        }
    }
}
impl PartialOrd for Span {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Serialize for Span {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        SerDedup::Untagged(self.unpack()).serialize(serializer)
    }
}
impl<'de> Deserialize<'de> for Span {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        use serde::de::Error;
        match SerDedup::<SerializedSpan>::deserialize(deserializer)? {
            SerDedup::Untagged(span) => Ok(Span::from_unpacked(span)),
            SerDedup::Value { .. } | SerDedup::Deduplicated { .. } => {
                Err(D::Error::custom(stateless_deserialize_error::<Span>()))
            }
        }
    }
}
impl<State: DedupSerializerState> SerializeState<State> for Span {
    fn serialize_state<S: serde::Serializer>(
        &self,
        state: &State,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        serialize_dedup(self, self.unpack(), state, serializer)
    }
}
impl<'de, State: DedupSerializerState> DeserializeState<'de, State> for Span {
    fn deserialize_state<D: serde::Deserializer<'de>>(
        state: &State,
        deserializer: D,
    ) -> Result<Self, D::Error> {
        deserialize_dedup(state, deserializer, Span::from_unpacked)
    }
}

impl std::fmt::Debug for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let span = self.unpack();
        f.debug_struct("Span")
            .field("data", &span.data)
            .field("generated_from_span", &span.generated_from_span)
            .finish()
    }
}

impl<'s, V> Drive<'s, V> for Span
where
    V: for<'a> Visit<'a, SerializedSpan> + for<'a> Visit<'a, Option<SerializedSpan>>,
{
    fn drive_inner(&'s self, v: &mut V) -> ControlFlow<V::Break> {
        v.visit(&self.unpack())
    }
}
impl<'s, V> DriveMut<'s, V> for Span
where
    V: for<'a> VisitMut<'a, SerializedSpan> + for<'a> VisitMut<'a, Option<SerializedSpan>>,
{
    fn drive_inner_mut(&'s mut self, v: &mut V) -> ControlFlow<V::Break> {
        let mut span = self.unpack();
        let res = v.visit(&mut span);
        *self = Span::from_unpacked(span);
        res
    }
}
impl<'s, V> DriveTwo<'s, V> for Span
where
    V: for<'a> VisitTwo<'a, SerializedSpan> + for<'a> VisitTwo<'a, Option<SerializedSpan>>,
{
    fn drive_two_inner(&'s self, other: &'s Self, v: &mut V) -> ControlFlow<V::Break> {
        v.visit(&self.unpack(), &other.unpack())
    }
}

/// Given a line number within a source file, get the byte of the start of the line. Obviously not
/// efficient to do many times, but this is used is diagnostic paths only. The line numer is
/// expected to be 1-based.
fn line_to_start_byte(source: &str, line_nbr: usize) -> usize {
    let mut cur_byte = 0;
    for (i, line) in source.split_inclusive('\n').enumerate() {
        if line_nbr == i + 1 {
            break;
        }
        cur_byte += line.len();
    }
    cur_byte
}

impl Loc {
    const fn dummy() -> Self {
        Loc { line: 0, col: 0 }
    }

    fn min(l0: &Loc, l1: &Loc) -> Loc {
        match l0.line.cmp(&l1.line) {
            Ordering::Equal => Loc {
                line: l0.line,
                col: std::cmp::min(l0.col, l1.col),
            },
            Ordering::Less => *l0,
            Ordering::Greater => *l1,
        }
    }

    fn max(l0: &Loc, l1: &Loc) -> Loc {
        match l0.line.cmp(&l1.line) {
            Ordering::Equal => Loc {
                line: l0.line,
                col: std::cmp::max(l0.col, l1.col),
            },
            Ordering::Greater => *l0,
            Ordering::Less => *l1,
        }
    }

    pub fn to_byte(self, source: &str) -> usize {
        line_to_start_byte(source, self.line as usize) + self.col as usize
    }
}

impl SpanData {
    pub const fn dummy() -> Self {
        SpanData {
            file_id: FileId::ZERO,
            beg: Loc::dummy(),
            end: Loc::dummy(),
        }
    }

    /// Value with which we order `SpanDatas`s.
    fn sort_key(&self) -> impl Ord {
        (self.file_id, self.beg, self.end)
    }

    pub fn to_byte_range(self, source: &str) -> Range<usize> {
        self.beg.to_byte(source)..self.end.to_byte(source)
    }
}

/// Manual impls because `SpanData` is not orderable.
impl PartialOrd for SpanData {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for SpanData {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.sort_key().cmp(&other.sort_key())
    }
}

impl Span {
    pub const fn dummy() -> Self {
        // Every field of `SpanData::dummy()` packs to zero, so this is just zero!
        // Actually tested below for correctness
        Span(0)
    }
}

/// Combine some span information (useful when we need to compute the
/// span-information of, say, a sequence).
pub fn combine_span(m0: &Span, m1: &Span) -> Span {
    let (d0, d1) = (m0.data(), m1.data());
    // Merge the spans
    if d0.file_id == d1.file_id {
        let data = SpanData {
            file_id: d0.file_id,
            beg: Loc::min(&d0.beg, &d1.beg),
            end: Loc::max(&d0.end, &d1.end),
        };

        // We don't attempt to merge the "generated from" spans: they might
        // come from different files, and even if they come from the same files
        // they might come from different macros, etc.
        Span::new(data, None)
    } else {
        // It happens that the spans don't come from the same file. In this
        // situation, we just return the first span. TODO: improve this.
        *m0
    }
}

/// Combine all the span information in a slice.
pub fn combine_span_iter<'a, T: Iterator<Item = &'a Span>>(mut ms: T) -> Span {
    // The iterator should have a next element
    let mut mc: Span = ms.next().copied().unwrap_or_default();
    for m in ms {
        mc = combine_span(&mc, m);
    }

    mc
}

impl FileName {
    pub fn to_string(&self) -> Cow<'_, str> {
        match self {
            FileName::Virtual(path_buf) | FileName::Local(path_buf) => path_buf.to_string_lossy(),
            FileName::NotReal(path) => Cow::Borrowed(path),
        }
    }
}

impl Default for Span {
    fn default() -> Self {
        Self::dummy()
    }
}

/// `Span` is stored inline in most ast nodes, so its size matters
#[test]
fn span_is_small() {
    assert_eq!(size_of::<Span>(), 8);
}

/// Check that `Span::dummy()` is correct.
#[test]
fn span_dummy_is_zero() {
    assert_eq!(Span::dummy(), Span::new(SpanData::dummy(), None));
    assert_eq!(Span::dummy().data(), SpanData::dummy());
}

/// Check that we roundtrip both the spans that fit the packed representation and the ones that
/// don't.
#[test]
fn span_roundtrip() {
    let data = |file: usize, beg: (u32, u32), end: (u32, u32)| SpanData {
        file_id: FileId::from_usize(file),
        beg: Loc {
            line: beg.0,
            col: beg.1,
        },
        end: Loc {
            line: end.0,
            col: end.1,
        },
    };
    let packed = data(12, (34, 56), (78, 90));
    let huge_file = data(1 << 20, (34, 56), (78, 90));
    let long_line = data(12, (34, 5678), (78, 90));
    let backwards = data(12, (78, 56), (34, 90));
    for (d, generated) in [
        (packed, None),
        (packed, Some(packed)),
        (huge_file, None),
        (long_line, None),
        (backwards, None),
    ] {
        let span = Span::new(d, generated);
        assert_eq!(span.data(), d);
        assert_eq!(span.generated_from_span(), generated);
    }
    // Only the first span above fits the packed representation.
    assert!(Span::new(packed, None).0 & pack::WIDE_FLAG == 0);
    // Equal spans have equal representations, even when they don't fit.
    assert_eq!(Span::new(backwards, None), Span::new(backwards, None));
}
