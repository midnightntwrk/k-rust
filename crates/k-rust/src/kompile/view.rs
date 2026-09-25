use std::{ops::Deref, sync::Arc};

/// A derived value that is either owned by a public one-shot helper or borrowed from a memo.
#[derive(Clone, Debug)]
pub(super) enum View<'a, T> {
    Owned(T),
    Shared(Arc<T>),
    Borrowed(&'a T),
}

impl<T> Deref for View<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        match self {
            Self::Owned(value) => value,
            Self::Shared(value) => value,
            Self::Borrowed(value) => value,
        }
    }
}
