//! Completion item generation.
//!
//! Given a cursor position (currently only context-free) we return a list of
//! candidates drawn from the symbol table plus the built-in keywords.

use crate::symbols::{SymbolKind, SymbolTable};

/// A single completion candidate returned by `completions_at`.
#[derive(Debug, Clone)]
pub struct CompletionItem {
    pub label: String,
    pub kind: CompletionKind,
    pub detail: Option<String>,
}

/// LSP-compatible completion item kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompletionKind {
    Keyword,
    Class,
    Interface,
    Individual,
    Function,
    Module,
}

static KEYWORDS: &[&str] = &[
    "concept", "property", "rule", "prefix",
    "sub", "has", "match", "then",
    "one", "any", "some", "optional",
    "string", "int", "float", "boolean",
    "all", "none", "at_least", "at_most", "exactly", "between",
];

/// Return all completion candidates relevant at the cursor.
///
/// `prefix` is the partial word already typed (may be empty).
pub fn completions_at(table: &SymbolTable, prefix: &str) -> Vec<CompletionItem> {
    let mut items: Vec<CompletionItem> = Vec::new();

    // Keywords.
    for kw in KEYWORDS {
        if kw.starts_with(prefix) {
            items.push(CompletionItem {
                label: kw.to_string(),
                kind: CompletionKind::Keyword,
                detail: None,
            });
        }
    }

    // Symbols from the table.
    for sym in table.iter() {
        if !sym.name.starts_with(prefix) {
            continue;
        }
        let kind = symbol_completion_kind(&sym.kind);
        items.push(CompletionItem {
            label: sym.name.clone(),
            kind,
            detail: Some(sym.detail.clone()),
        });
    }

    items.sort_by(|a, b| a.label.cmp(&b.label));
    items
}

fn symbol_completion_kind(kind: &SymbolKind) -> CompletionKind {
    match kind {
        SymbolKind::Concept => CompletionKind::Class,
        SymbolKind::Property => CompletionKind::Function,
        SymbolKind::Individual { .. } => CompletionKind::Individual,
        SymbolKind::Rule => CompletionKind::Interface,
        SymbolKind::Prefix => CompletionKind::Module,
    }
}
