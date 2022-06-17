use thiserror::Error;

pub trait Single: Iterator {
    fn single(self) -> Result<Self::Item, SingleError>;
}

#[derive(Debug, Error, PartialEq)]
pub enum SingleError {
    #[error("Called single() on empty iterator")]
    NoElements,
    #[error("Called single() on multiple-element iterator")]
    MultipleElements,
}

impl<I: Iterator> Single for I {
    fn single(mut self) -> Result<Self::Item, SingleError> {
        match self.next() {
            None => Err(SingleError::NoElements),
            Some(element) => match self.next() {
                None => Ok(element),
                Some(_) => Err(SingleError::MultipleElements),
            },
        }
    }
}

#[cfg(test)]
mod test {
    use super::{Single, SingleError};
    use std::iter;

    #[test]
    fn empty_error() {
        assert_eq!(iter::empty::<i32>().single(), Err(SingleError::NoElements));
    }

    #[test]
    fn multiple_error() {
        assert_eq!(iter::repeat(0).single(), Err(SingleError::MultipleElements));
    }

    #[test]
    fn single_success() {
        assert_eq!(iter::repeat(0).single(), Err(SingleError::MultipleElements));
    }
}
