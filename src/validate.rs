//! Semantic validation.
//!
//! Produces [`dolfin_diagnostic::Diagnostic`]s for structural problems:
//!
//! - **S001** Unresolved type reference
//! - **S002** Duplicate declaration name within the same file
//! - **S003** Circular inheritance (`concept A sub A`)

use std::collections::{HashMap, HashSet};

use dolfin_diagnostic::{Diagnostic, DiagnosticBuilder, DiagnosticCode};
use rowl::{Declaration, OntologyFile};

use crate::{index::SymbolIndex, resolve::ResolvedFile};

// ── Validation entry point ────────────────────────────────────────────────────

/// Run all structural validation checks and return every diagnostic found.
pub fn validate(
    file: &OntologyFile,
    _index: &SymbolIndex,
    resolved: &ResolvedFile,
) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    check_unresolved(resolved, &mut diags);
    check_duplicates(file, &mut diags);
    check_circular(file, &mut diags);
    diags
}

// ── Checks ────────────────────────────────────────────────────────────────────

fn check_unresolved(resolved: &ResolvedFile, diags: &mut Vec<Diagnostic>) {
    for r in resolved.unresolved() {
        diags.push(
            DiagnosticBuilder::error(
                DiagnosticCode::UNRESOLVED_TYPE,
                format!("type `{}` is not declared", r.name),
            )
            .span_opt(r.source_span.map(Into::into))
            .build(),
        );
    }
}

fn check_duplicates(file: &OntologyFile, diags: &mut Vec<Diagnostic>) {
    let mut seen: HashMap<&str, Option<rowl::error::Span>> = HashMap::new();
    for decl in &file.declarations {
        let (name, span) = decl_name_span(decl);
        if let Some(prev_span) = seen.get(name) {
            diags.push(
                DiagnosticBuilder::error(
                    DiagnosticCode::DUPLICATE_DECLARATION,
                    format!("duplicate declaration `{name}`"),
                )
                .span_opt(prev_span.map(Into::into))
                .build(),
            );
        } else {
            seen.insert(name, span);
        }
    }
}

fn check_circular(file: &OntologyFile, diags: &mut Vec<Diagnostic>) {
    let mut parents: HashMap<&str, Vec<String>> = HashMap::new();
    for decl in &file.declarations {
        if let Declaration::Concept(c) = decl {
            let ps = c
                .parents
                .iter()
                .filter_map(|p| match p {
                    rowl::TypeRef::Named { name, .. } => Some(name.last()),
                    _ => None,
                })
                .collect();
            parents.insert(c.name.get().as_str(), ps);
        }
    }

    for &start in parents.keys() {
        let mut visited = HashSet::new();
        let mut stack = vec![start];
        while let Some(node) = stack.pop() {
            if !visited.insert(node) {
                if node == start {
                    let span = file.declarations.iter().find_map(|d| {
                        if let Declaration::Concept(c) = d {
                            if c.name.get().as_str() == start { c.span } else { None }
                        } else {
                            None
                        }
                    });
                    diags.push(
                        DiagnosticBuilder::error(
                            DiagnosticCode::CIRCULAR_INHERITANCE,
                            format!("concept `{start}` has circular inheritance"),
                        )
                        .span_opt(span.map(Into::into))
                        .build(),
                    );
                }
                break;
            }
            if let Some(ps) = parents.get(node) {
                stack.extend(ps.iter().map(String::as_str));
            }
        }
    }
}

fn decl_name_span(decl: &Declaration) -> (&str, Option<rowl::error::Span>) {
    match decl {
        Declaration::Concept(c) => (c.name.get().as_str(), c.span),
        Declaration::Property(p) => (&p.name.get(), p.span),
        Declaration::Rule(r) => (&r.name, r.span),
    }
}

// ── Re-export for downstream crates that still import from here ───────────────
pub use dolfin_diagnostic::Severity;
