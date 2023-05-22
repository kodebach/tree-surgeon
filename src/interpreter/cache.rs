use std::{
    borrow::BorrowMut,
    ops::Range,
    path::{Path, PathBuf},
};

use ariadne::{Cache, Source};

use lazycell::LazyCell;
use tree_sitter::{Node, TextProvider};

pub type FileSpan = (PathBuf, Range<usize>);

pub struct SourceSliceRef<'a> {
    data: &'a [u8],
}

impl<'a> SourceSliceRef<'a> {
    pub fn get(&'a self) -> &'a [u8] {
        self.data
    }
}

impl<'a> AsRef<[u8]> for SourceSliceRef<'a> {
    fn as_ref(&self) -> &[u8] {
        self.get()
    }
}

pub trait SourceCache: Cache<PathBuf> {
    fn bytes(&self) -> SourceSliceRef;
    fn file(&self) -> &Path;

    fn translate_range(&self, range: Range<usize>) -> Range<usize>;

    fn update<F>(&mut self, update_fn: F)
    where
        F: FnOnce(&mut Vec<u8>);
}

#[derive(Clone)]
pub struct FileCache {
    bytes: Vec<u8>, // ropey::Rope
    source: LazyCell<Source>,
    file: PathBuf,
}

impl FileCache {
    pub fn new(bytes: Vec<u8>, file: PathBuf) -> FileCache {
        FileCache {
            bytes,
            source: LazyCell::new(),
            file,
        }
    }

    pub fn file(&self) -> &Path {
        self.file.as_path()
    }

    pub fn get_node_text(&self, node: Node) -> &[u8] {
        &self.bytes[node.byte_range()]
    }

    pub fn get_node_string(&self, node: Node) -> Result<&str, std::str::Utf8Error> {
        std::str::from_utf8(self.get_node_text(node))
    }
}

impl<'a> TextProvider<'a> for &'a FileCache {
    type I = std::iter::Once<&'a [u8]>;

    fn text(&mut self, node: Node) -> Self::I {
        std::iter::once(self.get_node_text(node))
    }
}

impl SourceCache for FileCache {
    fn bytes(&self) -> SourceSliceRef {
        SourceSliceRef {
            data: &self.bytes[0..self.bytes.len()],
        }
    }

    fn file(&self) -> &Path {
        &self.file
    }

    fn translate_range(&self, range: Range<usize>) -> Range<usize> {
        range
    }

    fn update<F>(&mut self, update_fn: F)
    where
        F: FnOnce(&mut Vec<u8>),
    {
        update_fn(self.bytes.borrow_mut());
    }
}

impl Cache<PathBuf> for FileCache {
    fn fetch(&mut self, id: &PathBuf) -> Result<&Source, Box<dyn std::fmt::Debug + '_>> {
        if id == &self.file {
            if !self.source.filled() {
                self.source
                    .fill(Source::from(String::from_utf8_lossy(self.bytes.as_slice())))
                    .unwrap();
            }

            Ok(self.source.borrow().unwrap())
        } else {
            Err(Box::new(format!(
                "Failed to fetch source '{}'",
                id.display()
            )))
        }
    }

    fn display<'a>(&self, id: &'a PathBuf) -> Option<Box<dyn std::fmt::Display + 'a>> {
        Some(Box::new(id.display()))
    }
}

#[derive(Clone)]
pub struct MacroCache {
    pub file_cache: FileCache,
    pub span: Range<usize>,
}

impl SourceCache for MacroCache {
    fn bytes(&self) -> SourceSliceRef {
        SourceSliceRef {
            data: &self.file_cache.bytes[self.span.clone()],
        }
    }

    fn file(&self) -> &Path {
        self.file_cache.file()
    }

    fn translate_range(&self, range: Range<usize>) -> Range<usize> {
        let offset = self.span.start;
        range.start + offset..range.end + offset
    }

    fn update<F>(&mut self, update_fn: F)
    where
        F: FnOnce(&mut Vec<u8>),
    {
        let mut macro_bytes = self.bytes().get().to_vec();
        update_fn(&mut macro_bytes);
        let new_span = self.span.start..self.span.start + macro_bytes.len();

        self.file_cache.borrow_mut().update(|bytes| {
            bytes.splice(self.span.clone(), macro_bytes);
        });
        self.span = new_span;
    }
}

impl Cache<PathBuf> for MacroCache {
    fn fetch(&mut self, id: &PathBuf) -> Result<&Source, Box<dyn std::fmt::Debug + '_>> {
        self.file_cache.borrow_mut().fetch(id)
    }

    fn display<'a>(&self, id: &'a PathBuf) -> Option<Box<dyn std::fmt::Display + 'a>> {
        Some(Box::new(id.display()))
    }
}
