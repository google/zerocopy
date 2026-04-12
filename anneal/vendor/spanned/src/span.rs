use bstr::{ByteSlice, Utf8Error};
use std::{
    fmt::{Debug, Display},
    io,
    ops::Range,
    path::PathBuf,
    str::FromStr,
};

#[derive(Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Spanned<T> {
    pub span: Span,
    pub content: T,
}

impl PartialEq<&str> for Spanned<&str> {
    fn eq(&self, other: &&str) -> bool {
        self.content.eq(*other)
    }
}

impl PartialEq<&str> for Spanned<String> {
    fn eq(&self, other: &&str) -> bool {
        self.content.eq(*other)
    }
}

impl<T> std::ops::Deref for Spanned<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.content
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for Spanned<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.span, f)?;
        write!(f, ": ")?;
        self.content.fmt(f)
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Span {
    pub file: PathBuf,
    pub bytes: Range<usize>,
}

impl Ord for Span {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.file
            .cmp(&other.file)
            .then_with(|| self.bytes.start.cmp(&other.bytes.start))
            .then_with(|| self.bytes.end.cmp(&other.bytes.end))
    }
}

impl PartialOrd for Span {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match self.file.partial_cmp(&other.file) {
            Some(core::cmp::Ordering::Equal) => {}
            ord => return ord,
        }
        match self.bytes.start.partial_cmp(&other.bytes.start) {
            Some(core::cmp::Ordering::Equal) => {}
            ord => return ord,
        }
        self.bytes.end.partial_cmp(&other.bytes.end)
    }
}

impl std::fmt::Debug for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}
impl Default for Span {
    #[track_caller]
    fn default() -> Self {
        Self {
            file: PathBuf::new(),
            bytes: usize::MAX..usize::MAX,
        }
    }
}

impl Span {
    /// Produce a span pointing into this Rust source file instead of into the file you are processing
    #[track_caller]
    pub fn here() -> Self {
        let info = std::panic::Location::caller();
        let Ok(file) = Spanned::read_from_file(info.file()).transpose() else {
            return Span {
                file: info.file().into(),
                bytes: 0..0,
            };
        };
        let Some(mut line) = file.lines().nth(info.line() as usize - 1) else {
            return Span {
                file: info.file().into(),
                bytes: 0..0,
            };
        };
        let Ok(col) = line.clone().to_str() else {
            return line.span;
        };
        let Some(col) = col.chars().nth(info.column() as usize - 1) else {
            return line.span;
        };
        line.span.bytes.start = col.span.bytes.start;
        line.span
    }

    pub fn is_dummy(&self) -> bool {
        self.bytes.start == usize::MAX && self.bytes.end == usize::MAX
    }
    #[track_caller]
    pub fn dec_col_end(mut self, amount: usize) -> Self {
        let new = self.bytes.end - amount;
        assert!(self.bytes.start <= new, "{self} new end: {new}");
        self.bytes.end = new;
        self
    }
    #[track_caller]
    pub fn inc_col_start(mut self, amount: usize) -> Self {
        let new = self.bytes.start + amount;
        assert!(new <= self.bytes.end, "{self} new end: {new}");
        self.bytes.start = new;
        self
    }
    #[track_caller]
    pub fn set_col_end_relative_to_start(mut self, amount: usize) -> Self {
        let new = self.bytes.start + amount;
        assert!(new <= self.bytes.end, "{self} new end: {new}");
        self.bytes.end = new;
        self
    }
    pub fn shrink_to_end(mut self) -> Span {
        self.bytes.start = self.bytes.end;
        self
    }

    pub fn shrink_to_start(mut self) -> Span {
        self.bytes.end = self.bytes.start;
        self
    }
}

impl Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.file == PathBuf::new() {
            return write!(f, "DUMMY_SPAN");
        }
        let Self { file, bytes } = self;
        let file = file.display();
        write!(f, "{file}[{}..{}]", bytes.start, bytes.end)
    }
}

impl Spanned<&str> {
    pub fn split_once(&self, delimiter: &str) -> Option<(Self, Self)> {
        let (a, b) = self.content.split_once(delimiter)?;
        let span = self.span.clone().dec_col_end(b.len());
        let a = Spanned { span, content: a };
        let span = self.span.clone().inc_col_start(a.len() + 1);
        let b = Spanned { span, content: b };
        Some((a, b))
    }

    pub fn take_while(&self, delimiter: impl Fn(char) -> bool) -> Option<(Self, Self)> {
        let pos = self.content.find(|c| !delimiter(c))?;
        Some(self.split_at(pos))
    }

    pub fn split_at(&self, pos: usize) -> (Self, Self) {
        let (a, b) = self.content.split_at(pos);
        let n = a.len();
        let span = self.span.clone().set_col_end_relative_to_start(n);
        let a = Spanned { span, content: a };
        let span = self.span.clone().inc_col_start(n);
        let b = Spanned { span, content: b };
        (a, b)
    }

    pub fn trim_end(&self) -> Self {
        let content = self.content.trim_end();
        let n = self.content[content.len()..].len();
        let span = self.span.clone().dec_col_end(n);
        Self { content, span }
    }

    pub fn is_empty(&self) -> bool {
        self.content.is_empty()
    }

    pub fn strip_prefix(&self, prefix: &str) -> Option<Self> {
        let content = self.content.strip_prefix(prefix)?;
        let span = self.span.clone().inc_col_start(prefix.len());
        Some(Self { content, span })
    }

    pub fn strip_suffix(&self, suffix: &str) -> Option<Self> {
        let content = self.content.strip_suffix(suffix)?;
        let span = self.span.clone().dec_col_end(suffix.len());
        Some(Self { span, content })
    }

    pub fn trim_start(&self) -> Self {
        let content = self.content.trim_start();
        let n = self.content[..(self.content.len() - content.len())].len();
        let span = self.span.clone().inc_col_start(n);
        Self { content, span }
    }

    pub fn trim_start_matches(&self, c: char) -> Self {
        let content = self.content.trim_start_matches(c);
        let n = self.content[..(self.content.len() - content.len())].len();
        let span = self.span.clone().inc_col_start(n);
        Self { content, span }
    }

    pub fn trim(&self) -> Self {
        self.trim_start().trim_end()
    }

    pub fn starts_with(&self, pat: &str) -> bool {
        self.content.starts_with(pat)
    }

    pub fn chars(&self) -> impl Iterator<Item = Spanned<char>> + '_ {
        self.content.char_indices().map(move |(i, c)| {
            Spanned::new(c, self.span.clone().inc_col_start(i).shrink_to_start())
        })
    }

    pub fn split(&self, needle: char) -> impl Iterator<Item = Spanned<&str>> + Clone + '_ {
        let mut start = 0;
        self.content
            .char_indices()
            .chain([(self.content.len(), needle)])
            .filter_map(move |(i, c)| {
                if c == needle {
                    let content = &self.content[start..i];
                    let span = self
                        .span
                        .clone()
                        .inc_col_start(start)
                        .set_col_end_relative_to_start(content.len());
                    start = i + 1;

                    Some(Spanned::new(content, span))
                } else {
                    None
                }
            })
    }

    pub fn to_string(&self) -> Spanned<String> {
        Spanned {
            span: self.span.clone(),
            content: self.content.to_string(),
        }
    }
}

impl<'a> Spanned<&'a [u8]> {
    pub fn strip_prefix(&self, prefix: &[u8]) -> Option<Self> {
        let content = self.content.strip_prefix(prefix)?;
        let span = self.span.clone().inc_col_start(prefix.len());
        Some(Self { span, content })
    }

    pub fn split_once_str(&self, splitter: &str) -> Option<(Self, Self)> {
        let (a, b) = self.content.split_once_str(splitter)?;
        Some((
            Self {
                content: a,
                span: self.span.clone().set_col_end_relative_to_start(a.len()),
            },
            Self {
                content: b,
                span: self.span.clone().inc_col_start(a.len() + splitter.len()),
            },
        ))
    }

    pub fn to_str(self) -> Result<Spanned<&'a str>, Spanned<Utf8Error>> {
        let span = self.span;
        match self.content.to_str() {
            Ok(content) => Ok(Spanned { content, span }),
            Err(err) => Err(Spanned { content: err, span }),
        }
    }
}

impl<T: Display> Spanned<T> {
    pub fn render(&self) -> String {
        let Ok(file) = Spanned::read_str_from_file(&self.span.file).transpose() else {
            return format!("{}: {}", self.span.file.display(), self.content);
        };
        let Some((l, line)) = file
            .lines()
            .enumerate()
            .find(|(_, l)| l.span.bytes.contains(&self.span.bytes.start))
        else {
            return format!("{}: {}", self.span.file.display(), self.content);
        };
        let Ok(line) = line.to_str() else {
            return format!("{}: {}", self.span.file.display(), self.content);
        };
        let Some(c) = line
            .chars()
            .position(|c| c.span.bytes.start == self.span.bytes.start)
        else {
            return format!("{}: {}", self.span.file.display(), self.content);
        };
        format!(
            "{}:{}:{}: {}",
            self.span.file.display(),
            l + 1,
            c + 1,
            self.content
        )
    }
}

impl<T> Spanned<T> {
    pub fn new(content: T, span: Span) -> Self {
        Self { content, span }
    }
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Spanned<U> {
        let Spanned { content, span } = self;
        let content = f(content);
        Spanned { content, span }
    }

    #[track_caller]
    pub fn here(content: T) -> Self {
        Self {
            span: Span::here(),
            content,
        }
    }

    pub fn dummy(content: T) -> Self {
        Self {
            span: Span::default(),
            content,
        }
    }

    pub fn span(&self) -> Span {
        self.span.clone()
    }

    pub fn as_ref<U: ?Sized>(&self) -> Spanned<&U>
    where
        T: AsRef<U>,
    {
        Spanned {
            span: self.span.clone(),
            content: self.content.as_ref(),
        }
    }
}

impl<T, E> Spanned<Result<T, E>> {
    pub fn transpose(self) -> Result<Spanned<T>, Spanned<E>> {
        match self.content {
            Ok(val) => Ok(Spanned::new(val, self.span)),
            Err(err) => Err(Spanned::new(err, self.span)),
        }
    }
}

impl<T, E: Debug> Spanned<Result<T, E>> {
    pub fn unwrap(self) -> Spanned<T> {
        self.transpose().unwrap()
    }
}

impl Spanned<Vec<u8>> {
    pub fn read_from_file(path: impl Into<PathBuf>) -> Spanned<io::Result<Vec<u8>>> {
        let path = path.into();
        let content = std::fs::read(&path);
        let len = content.as_ref().map(|c| c.len()).unwrap_or(0);
        let span = Span {
            file: path,
            bytes: 0..len,
        };
        Spanned { span, content }
    }
}

impl Spanned<String> {
    pub fn read_str_from_file(path: impl Into<PathBuf>) -> Spanned<io::Result<String>> {
        let path = path.into();
        let content = std::fs::read_to_string(&path);
        let len = content.as_ref().map(|c| c.len()).unwrap_or(0);
        let span = Span {
            file: path,
            bytes: 0..len,
        };
        Spanned { span, content }
    }
}

impl<T: AsRef<[u8]>> Spanned<T> {
    /// Split up the string into lines
    pub fn lines(&self) -> impl Iterator<Item = Spanned<&[u8]>> {
        let content = self.content.as_ref();
        content.lines().map(move |line| {
            let span = self.span.clone();
            // SAFETY: `line` is a substr of `content`, so the `offset_from` requirements are
            // trivially satisfied.
            let amount = unsafe { line.as_ptr().offset_from(content.as_ptr()) };
            let mut span = span.inc_col_start(amount.try_into().unwrap());
            span.bytes.end = span.bytes.start + line.len();
            Spanned {
                content: line,
                span,
            }
        })
    }
}

impl<S: AsRef<str>> Spanned<S> {
    pub fn parse<T: FromStr>(&self) -> Spanned<Result<T, T::Err>> {
        let content = self.content.as_ref().parse();
        Spanned {
            span: self.span.clone(),
            content,
        }
    }
}

impl<T: Display> From<Spanned<T>> for anyhow::Error {
    fn from(s: Spanned<T>) -> anyhow::Error {
        anyhow::anyhow!("{}", s.render())
    }
}

impl<T: Display> From<Spanned<T>> for color_eyre::eyre::Error {
    fn from(s: Spanned<T>) -> color_eyre::eyre::Error {
        color_eyre::eyre::eyre!("{}", s.render())
    }
}
