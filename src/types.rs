//! Type-level validation.
//!
//! Checks that types are used *correctly*, not merely that they exist
//! (existence is handled by [`crate::resolve`] + [`crate::validate`]).
//!
//! Rules checked here:
//!
//! - **S004** A `sub` parent is not a concept (e.g. it's an enum).
//! - **S005** A property domain is not a concept.
//! - **S006** A cardinality range has `min > max`.

use dolfin_diagnostic::{Diagnostic, DiagnosticBuilder, DiagnosticCode};
use rowl::{Cardinality, Declaration, OntologyFile, TypeRef, error::Span};

use crate::index::{SymbolIndex, SymbolKind};

/// Run all type-level checks and return diagnostics.
pub fn check_types(file: &OntologyFile, index: &SymbolIndex) -> Vec<Diagnostic> {
    let mut diags = Vec::new();

    for decl in &file.declarations {
        match decl {
            Declaration::Concept(c) => {
                for parent in &c.parents {
                    check_is_concept_type_ref(parent, index, 4, &|name, kind| {
                        format!(
                            "`{name}` is a {kind}, not a concept; \
                             only concepts can appear after `sub`"
                        )
                    }, &mut diags);
                }

                for has in &c.has_declarations {
                    if let Some(card) = &has.cardinality {
                        check_cardinality(card, has.span, &mut diags);
                    }
                }
            }

            Declaration::Property(p) => {
                check_is_concept_type_ref(&p.domain, index, 5, &|name, kind| {
                    format!("property domain `{name}` must be a concept, not a {kind}")
                }, &mut diags);

                if let Some(card) = &p.domain_cardinality {
                    check_cardinality(card, p.span, &mut diags);
                }
                if let Some(card) = &p.range_cardinality {
                    check_cardinality(card, p.span, &mut diags);
                }
            }

            Declaration::Rule(_) => {}
            Declaration::Fact(_) => {}
            Declaration::Query(_) => {}
            Declaration::Unit(_) => {}
        }
    }

    diags
}

/// Checks a (possibly `Union`) type reference names only concepts, recursing
/// into every union member so `(A or B)` is checked member-by-member.
fn check_is_concept_type_ref(
    type_ref: &TypeRef,
    index: &SymbolIndex,
    code: u16,
    msg: &dyn Fn(&str, &str) -> String,
    diags: &mut Vec<Diagnostic>,
) {
    match type_ref {
        TypeRef::Named { name, span } => {
            let resolved = index.get(&name.last()).or_else(|| index.get(&name.full()));
            if let Some(sym) = resolved
                && sym.kind != SymbolKind::Concept {
                    diags.push(
                        DiagnosticBuilder::error(
                            DiagnosticCode::Semantic(code),
                            msg(&name.last(), kind_label(&sym.kind)),
                        )
                        .span_opt(span.map(Into::into))
                        .build(),
                    );
                }
        }
        TypeRef::Union { members, .. } => {
            for m in members {
                check_is_concept_type_ref(m, index, code, msg, diags);
            }
        }
        TypeRef::Primitive { .. } => {}
    }
}

fn check_cardinality(card: &Cardinality, span: Option<Span>, diags: &mut Vec<Diagnostic>) {
    if let Cardinality::Range {
        min,
        max: Some(max),
        ..
    } = card
        && min > max {
            diags.push(
                DiagnosticBuilder::error(
                    DiagnosticCode::Semantic(6),
                    format!("invalid cardinality range {min}..{max}: min must be ≤ max"),
                )
                .span_opt(span.map(Into::into))
                .build(),
            );
        }
}

fn kind_label(kind: &SymbolKind) -> &'static str {
    match kind {
        SymbolKind::Concept => "concept",
        SymbolKind::Property => "property",
        SymbolKind::Rule => "rule",
        SymbolKind::Query => "query",
        SymbolKind::Prefix => "prefix",
        SymbolKind::Individual { .. } => "individual",
        SymbolKind::FactInstance => "fact",
    }
}
