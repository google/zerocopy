use bstr::{ByteSlice, Utf8Error};
use color_eyre::{eyre::Context, Report, Result};
use std::{fmt::Display, ops::Range, path::PathBuf, str::FromStr};

#[derive(Clone, Default)]
pub struct Spanned<T> {
    pub span: Span,
    pub content: T,
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

impl std::fmt::Debug for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}
impl Default for Span {
    fn default() -> Self {
        Self {
            file: PathBuf::new(),
            bytes: usize::MAX..usize::MAX,
        }
    }
}

impl Span {
    pub fn is_dummy(&self) -> bool {
        self == &Self::default()
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
        if self.is_dummy() {
            return write!(f, "DUMMY_SPAN");
        }
        let Self { file, bytes } = self;
        let file = file.display();
        write!(f, "{file}:{}:{}", bytes.start, bytes.end)
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

    pub fn trim(&self) -> Self {
        self.trim_start().trim_end()
    }

    pub fn starts_with(&self, pat: &str) -> bool {
        self.content.starts_with(pat)
    }

    pub fn parse<T: FromStr>(self) -> Result<Spanned<T>>
    where
        T::Err: Into<Report>,
    {
        let content = self
            .content
            .parse()
            .map_err(Into::into)
            .with_context(|| self.span.clone())?;
        Ok(Spanned {
            span: self.span,
            content,
        })
    }

    pub fn chars(&self) -> impl Iterator<Item = Spanned<char>> + '_ {
        self.content.chars().enumerate().map(move |(i, c)| {
            Spanned::new(c, self.span.clone().inc_col_start(i).shrink_to_start())
        })
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

impl<T> Spanned<T> {
    pub fn new(content: T, span: Span) -> Self {
        Self { content, span }
    }
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Spanned<U> {
        let Spanned { content, span } = self;
        let content = f(content);
        Spanned { content, span }
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

impl Spanned<Vec<u8>> {
    pub fn read_from_file(path: impl Into<PathBuf>) -> Result<Self> {
        let path = path.into();
        let path_str = path.display().to_string();
        let content = std::fs::read(&path).with_context(|| path_str)?;
        let span = Span {
            file: path,
            bytes: 0..content.len(),
        };
        Ok(Self { span, content })
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
