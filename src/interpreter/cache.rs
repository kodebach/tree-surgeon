use std::{
    fmt::Debug,
    ops::Range,
    path::{Path, PathBuf},
};

use miette::SourceSpan;
use ropey::{Rope, RopeSlice};
use tree_sitter::Node;

pub trait SourceCache: Debug + ToString {
    fn file(&self) -> &Path;

    fn translate_span(&self, span: SourceSpan) -> SourceSpan;

    fn get_node_string(&self, node: Node) -> String;

    fn parse(
        &self,
        parser: &mut tree_sitter::Parser,
        old_tree: Option<&tree_sitter::Tree>,
    ) -> Option<tree_sitter::Tree>;

    fn write_to(&self, target: &mut impl std::io::Write) -> std::io::Result<()>;
}

#[derive(Debug)]
pub struct FileCache {
    rope: Rope,
    file: PathBuf,
}

impl FileCache {
    pub fn new(rope: Rope, file: PathBuf) -> FileCache {
        FileCache { rope, file }
    }

    pub fn file(&self) -> &Path {
        self.file.as_path()
    }

    pub fn get_node_string(&self, node: Node) -> String {
        return self.rope.byte_slice(node.byte_range()).to_string();
    }

    pub fn apply_edit(&mut self, byte_range: Range<usize>, new_text: &str) {
        let start_char = self.rope.byte_to_char(byte_range.start);
        let old_end_char = self.rope.byte_to_char(byte_range.end);
        self.rope.remove(start_char..old_end_char);
        self.rope.insert(start_char, new_text);
    }
}

trait TextProvider<'a>: tree_sitter::TextProvider<'a> {}

impl<'a, C> TextProvider<'a> for &'a C
where
    C: SourceCache,
    &'a C: TextProvider<'a>,
{
}

impl<'a> tree_sitter::TextProvider<'a> for &'a FileCache {
    type I = Chunks<'a>;

    fn text(&mut self, node: Node) -> Self::I {
        let chunks = self.rope.byte_slice(node.byte_range()).chunks();
        Chunks { chunks }
    }
}

impl<'a> Iterator for Chunks<'a> {
    type Item = &'a [u8];

    fn next(&mut self) -> Option<Self::Item> {
        self.chunks.next().map(str::as_bytes)
    }
}

pub struct Chunks<'a> {
    chunks: ropey::iter::Chunks<'a>,
}

impl SourceCache for FileCache {
    fn file(&self) -> &Path {
        &self.file
    }

    fn translate_span(&self, span: SourceSpan) -> SourceSpan {
        span
    }

    fn get_node_string(&self, node: Node) -> String {
        self.rope.byte_slice(node.byte_range()).to_string()
    }

    fn parse(
        &self,
        parser: &mut tree_sitter::Parser,
        old_tree: Option<&tree_sitter::Tree>,
    ) -> Option<tree_sitter::Tree> {
        let mut callback = |offset, _| {
            let (chunk, chunk_byte_index, _, _) = self.rope.chunk_at_byte(offset);
            &chunk[(offset - chunk_byte_index)..]
        };
        parser.parse_with(&mut callback, old_tree)
    }

    fn write_to(&self, target: &mut impl std::io::Write) -> std::io::Result<()> {
        self.rope.write_to(target)
    }
}

impl ToString for FileCache {
    fn to_string(&self) -> String {
        self.rope.to_string()
    }
}

#[derive(Debug)]
pub struct MacroCache {
    file: PathBuf,
    rope: Rope,
    range: Range<usize>,
}

impl MacroCache {
    pub fn new(file_cache: &FileCache, range: Range<usize>) -> Self {
        let rope = file_cache.rope.clone();
        let start_line = rope.byte_to_line(range.start);
        let end_line = rope.byte_to_line(range.end);

        let start_col = rope.byte_to_char(range.start) - rope.line_to_char(start_line);
        let end_col = rope.byte_to_char(range.end) - rope.line_to_char(end_line);

        MacroCache {
            file: PathBuf::from(format!(
                "{}@{}:{}-{}:{}",
                file_cache.file.to_string_lossy(),
                start_line,
                start_col,
                end_line,
                end_col
            )),
            rope,
            range,
        }
    }

    pub fn translate_range(&self, range: Range<usize>) -> Range<usize> {
        let offset = self.range.start;
        range.start + offset..range.end + offset
    }

    fn rope_slice(&self) -> RopeSlice {
        self.rope.byte_slice(self.range.clone())
    }
}

impl SourceCache for MacroCache {
    fn file(&self) -> &Path {
        &self.file
    }

    fn translate_span(&self, span: SourceSpan) -> SourceSpan {
        SourceSpan::new((span.offset() + self.range.start).into(), span.len().into())
    }

    fn get_node_string(&self, node: Node) -> String {
        self.rope_slice().byte_slice(node.byte_range()).to_string()
    }

    fn parse(
        &self,
        parser: &mut tree_sitter::Parser,
        old_tree: Option<&tree_sitter::Tree>,
    ) -> Option<tree_sitter::Tree> {
        let mut callback = |offset, _| {
            let (chunk, chunk_byte_index, _, _) = self.rope_slice().chunk_at_byte(offset);
            &chunk[(offset - chunk_byte_index)..]
        };
        parser.parse_with(&mut callback, old_tree)
    }

    fn write_to(&self, target: &mut impl std::io::Write) -> std::io::Result<()> {
        for chunk in self.rope_slice().chunks() {
            target.write_all(chunk.as_bytes())?;
        }

        Ok(())
    }
}

impl ToString for MacroCache {
    fn to_string(&self) -> String {
        self.rope_slice().to_string()
    }
}

impl<'a> tree_sitter::TextProvider<'a> for &'a MacroCache {
    type I = Chunks<'a>;

    fn text(&mut self, node: Node) -> Self::I {
        let chunks = self.rope_slice().byte_slice(node.byte_range()).chunks();
        Chunks { chunks }
    }
}
