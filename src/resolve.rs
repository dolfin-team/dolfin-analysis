//! Name resolution.
//!
//! Given a parsed `OntologyFile` and a `SymbolIndex`, walks every `TypeRef`
//! in the file and attempts to resolve it to a symbol in the index.
//!
//! The resulting `ResolvedFile` is consumed by [`crate::validate`] and
//! [`crate::types`] to produce diagnostics.

use rowl::{Declaration, HasDeclaration, OntologyFile, TypeRef, error::Span};

use crate::index::SymbolIndex;

// ── ResolvedRef ───────────────────────────────────────────────────────────────

/// A single name reference found in the source and its resolution outcome.
#[derive(Debug, Clone)]
pub struct ResolvedRef {
    /// The name as written in source (last component of a qualified name).
    pub name: String,
    /// Source span of the reference (not the definition).
    pub source_span: Option<Span>,
    /// The canonical name in the index, if resolution succeeded.
    pub resolved: Option<String>,
}

impl ResolvedRef {
    pub fn is_unresolved(&self) -> bool {
        self.resolved.is_none()
    }
}

// ── ResolvedFile ──────────────────────────────────────────────────────────────

/// All resolved (and unresolved) name references in a single file.
#[derive(Debug, Default)]
pub struct ResolvedFile {
    pub refs: Vec<ResolvedRef>,
}

impl ResolvedFile {
    /// All references that failed to resolve.
    pub fn unresolved(&self) -> impl Iterator<Item = &ResolvedRef> {
        self.refs.iter().filter(|r| r.is_unresolved())
    }

    /// All references that resolved successfully.
    pub fn resolved(&self) -> impl Iterator<Item = &ResolvedRef> {
        self.refs.iter().filter(|r| !r.is_unresolved())
    }
}

// ── Resolution pass ───────────────────────────────────────────────────────────

/// Walk all type references in `file` and resolve them against `index`.
pub fn resolve_file(file: &OntologyFile, index: &SymbolIndex) -> ResolvedFile {
    let mut result = ResolvedFile::default();

    for decl in &file.declarations {
        match decl {
            Declaration::Concept(c) => {
                for parent in &c.parents {
                    resolve_type_ref(parent, index, &mut result);
                }
                for has in &c.has_declarations {
                    resolve_has(has, index, &mut result);
                }
            }
            Declaration::Property(p) => {
                resolve_type_ref(&p.domain, index, &mut result);
                resolve_type_ref(&p.range, index, &mut result);
            }
            Declaration::Rule(_) => {}
        }
    }

    result
}

fn resolve_has(has: &HasDeclaration, index: &SymbolIndex, out: &mut ResolvedFile) {
    resolve_type_ref(&has.type_ref, index, out);
}

fn resolve_type_ref(type_ref: &TypeRef, index: &SymbolIndex, out: &mut ResolvedFile) {
    let TypeRef::Named { name, span } = type_ref else {
        // Primitives are always resolved.
        return;
    };

    let full = name.full();
    let last = name.last();

    // Try unqualified last segment first, then the full qualified name.
    let resolved = if index.get(&last).is_some() {
        Some(last.clone())
    } else if index.get(&full).is_some() {
        Some(full.clone())
    } else {
        None
    };

    out.refs.push(ResolvedRef {
        name: full,
        source_span: *span,
        resolved,
    });
}
