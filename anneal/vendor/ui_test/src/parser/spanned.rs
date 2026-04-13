pub(crate) use spanned::*;

/// An optional spanned value.
#[derive(Debug, Clone)]
pub struct OptWithLine<T>(Option<Spanned<T>>);

impl<T> std::ops::Deref for OptWithLine<T> {
    type Target = Option<Spanned<T>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> From<Option<Spanned<T>>> for OptWithLine<T> {
    fn from(value: Option<Spanned<T>>) -> Self {
        Self(value)
    }
}

impl<T> From<Spanned<T>> for OptWithLine<T> {
    fn from(value: Spanned<T>) -> Self {
        Self(Some(value))
    }
}

impl<T> Default for OptWithLine<T> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<T> OptWithLine<T> {
    /// Creates a new optional spanned value.
    pub fn new(data: T, span: Span) -> Self {
        Self(Some(Spanned::new(data, span)))
    }

    /// Tries to set the value if not already set. Returns newly passed
    /// value in case there was already a value there.
    #[must_use]
    pub fn set(&mut self, data: T, span: Span) -> Option<Spanned<T>> {
        let new = Spanned::new(data, span);
        if self.0.is_some() {
            Some(new)
        } else {
            self.0 = Some(new);
            None
        }
    }

    /// Consumes `self` and returns the inner value.
    #[must_use]
    pub fn into_inner(self) -> Option<Spanned<T>> {
        self.0
    }
}
