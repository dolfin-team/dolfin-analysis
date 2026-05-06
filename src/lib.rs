//! Semantic analysis for the Dolfin ontology language.
//!
//! # Architecture
//!
//! ```text
//! rowl::parse_ontology(source)
//!         │
//!         ▼
//! index::SymbolIndex::from_file(file)   ← all declared symbols
//!         │
//!         ▼
//! resolve::resolve_file(file, &index)   ← every TypeRef resolved or flagged
//!         │
//!         ├─▶ validate::validate(...)   ← structural errors (E001–E003)
//!         │
//!         └─▶ types::check_types(...)   ← type-level errors (E004–E006)
//! ```
//!
//! # Quick start
//!
//! ```no_run
//! use rowl::parser::parse_ontology;
//! use dolfin_analysis::analyze;
//!
//! let result = parse_ontology("concept Person:\n  has name: string\n");
//! if let Some(file) = result.ontology {
//!     let analysis = analyze(file);
//!     for diag in &analysis.diagnostics {
//!         eprintln!("[{}] {}", diag.code.code_str(), diag.message);
//!     }
//! }
//! ```

pub mod diagnostics;
pub mod index;
pub mod references;
pub mod resolve;
pub mod types;
pub mod validate;

// ── Re-exports ────────────────────────────────────────────────────────────────

pub use dolfin_diagnostic::{Diagnostic, DiagnosticCode, Severity};
pub use index::{Symbol, SymbolIndex, SymbolKind};

// ── Analysis result ───────────────────────────────────────────────────────────

/// Everything produced by a full semantic analysis pass on one file.
pub struct AnalysisResult {
    /// All symbols declared in the file (and any previously indexed files).
    pub index: SymbolIndex,
    /// Semantic diagnostics (resolve + validate + type checks).
    pub diagnostics: Vec<Diagnostic>,
}

// ── Entry point ───────────────────────────────────────────────────────────────

/// Run a complete semantic analysis on a parsed ontology file.
///
/// To analyse a file in the context of a workspace, build a `SymbolIndex`
/// with `add_file` across all open files and call [`analyze_with_index`].
pub fn analyze(file: rowl::OntologyFile) -> AnalysisResult {
    let index = SymbolIndex::from_file(&file);
    analyze_with_index(file, index)
}

/// Analyse a file using a pre-built (potentially multi-file) index.
///
/// This is the workspace-aware variant: the caller builds the `SymbolIndex`
/// from all known files and passes it in so cross-file references resolve.
pub fn analyze_with_index(file: rowl::OntologyFile, index: SymbolIndex) -> AnalysisResult {
    let resolved = resolve::resolve_file(&file, &index);

    let mut diagnostics = validate::validate(&file, &index, &resolved);
    diagnostics.extend(types::check_types(&file, &index));

    AnalysisResult { index, diagnostics }
}
