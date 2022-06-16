use thiserror::Error;

pub trait Single: Iterator {
    fn single(self) -> Result<Self::Item, Error>;
}

#[derive(Debug, Error)]
pub enum Error {
    #[error("Called single() on empty iterator")]
    NoElements,
    #[error("Called single() on multiple-element iterator")]
    MultipleElements,
}

impl<I: Iterator> Single for I {
    fn single(mut self) -> Result<Self::Item, Error> {
        match self.next() {
            None => Err(Error::NoElements),
            Some(element) => match self.next() {
                None => Ok(element),
                Some(_) => Err(Error::MultipleElements),
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
