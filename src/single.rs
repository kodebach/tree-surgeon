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
    use super::Single;
    use std::iter;

    #[test]
    #[should_panic(expected = "Called single() on empty iterator")]
    fn panic_empty() {
        let _: i32 = iter::empty().single().unwrap();
    }

    #[test]
    #[should_panic(expected = "Called single() on multiple-element iterator")]
    fn panic_multiple() {
        let _ = iter::repeat(0).single().unwrap();
    }
}
