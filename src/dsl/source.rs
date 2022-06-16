use miette::{SourceCode, SourceSpan, SpanContents, MietteError, MietteSpanContents};

#[derive(Debug)]
pub struct NamedSource {
    pub source: String,
    name: String,
}

impl NamedSource {
    /// Create a new `NamedSource` using a regular [`SourceCode`] and giving
    /// its returned [`SpanContents`] a name.
    pub fn new(name: impl AsRef<str>, source: impl AsRef<str>) -> Self {
        Self {
            source: source.as_ref().to_string(),
            name: name.as_ref().to_string(),
        }
    }

    pub fn source<'a>(self: &'a Self) -> &'a str {
        self.source.as_str()
    }
}

impl SourceCode for NamedSource {
    fn read_span<'a>(
        &'a self,
        span: &SourceSpan,
        context_lines_before: usize,
        context_lines_after: usize,
    ) -> Result<Box<dyn SpanContents<'a> + 'a>, MietteError> {
        let contents = self
            .source
            .read_span(span, context_lines_before, context_lines_after)?;
        Ok(Box::new(MietteSpanContents::new_named(
            self.name.clone(),
            contents.data(),
            *contents.span(),
            contents.line(),
            contents.column(),
            contents.line_count(),
        )))
    }
}