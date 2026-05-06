//! Main analysis entry point.
//!
//! `Analyzer::run` takes a freshly-parsed `OntologyFile` and produces an
//! `AnalysisResult` that bundles the symbol table, semantic diagnostics, and
//! helpers for hover / completion.

use rowl::OntologyFile;

use crate::{
    completion::{CompletionItem, completions_at},
    diagnostics::Diagnostic,
    hover::hover_at,
    resolver,
    symbols::SymbolTable,
};
use rowl::error::Location;

/// The output of a full semantic analysis pass.
pub struct AnalysisResult {
    /// All symbols declared in the file.
    pub symbols: SymbolTable,
    /// Semantic diagnostics (in addition to parse errors from rowl).
    pub diagnostics: Vec<Diagnostic>,
    /// Keep a clone of the parsed file so hover/completion can walk the AST.
    file: OntologyFile,
}

impl AnalysisResult {
    /// Look up hover information for a position given as a `Location`.
    pub fn hover(&self, position: Location) -> Option<String> {
        hover_at(&self.file, &self.symbols, position)
    }

    /// Return completion candidates matching `prefix` (may be empty for all).
    pub fn completions(&self, prefix: &str) -> Vec<CompletionItem> {
        completions_at(&self.symbols, prefix)
    }
}

/// Run a full semantic analysis on a parsed ontology file.
pub fn analyze(file: OntologyFile) -> AnalysisResult {
    let symbols = SymbolTable::build(&file);
    let diagnostics = resolver::resolve(&file, &symbols);

    AnalysisResult { symbols, diagnostics, file }
}
