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
                    if let TypeRef::Named { name, span } = parent {
                        let resolved = index.get(&name.last()).or_else(|| index.get(&name.full()));
                        if let Some(sym) = resolved {
                            if sym.kind != SymbolKind::Concept {
                                diags.push(
                                    DiagnosticBuilder::error(
                                        DiagnosticCode::Semantic(4),
                                        format!(
                                            "`{}` is a {}, not a concept; \
                                             only concepts can appear after `sub`",
                                            name.last(),
                                            kind_label(&sym.kind),
                                        ),
                                    )
                                    .span_opt(span.map(Into::into))
                                    .build(),
                                );
                            }
                        }
                    }
                }

                for has in &c.has_declarations {
                    if let Some(card) = &has.cardinality {
                        check_cardinality(card, has.span, &mut diags);
                    }
                }
            }

            Declaration::Property(p) => {
                if let TypeRef::Named { name, span } = &p.domain {
                    let resolved = index.get(&name.last()).or_else(|| index.get(&name.full()));
                    if let Some(sym) = resolved {
                        if sym.kind != SymbolKind::Concept {
                            diags.push(
                                DiagnosticBuilder::error(
                                    DiagnosticCode::Semantic(5),
                                    format!(
                                        "property domain `{}` must be a concept, not a {}",
                                        name.last(),
                                        kind_label(&sym.kind),
                                    ),
                                )
                                .span_opt(span.map(Into::into))
                                .build(),
                            );
                        }
                    }
                }

                if let Some(card) = &p.domain_cardinality {
                    check_cardinality(card, p.span, &mut diags);
                }
                if let Some(card) = &p.range_cardinality {
                    check_cardinality(card, p.span, &mut diags);
                }
            }

            Declaration::Rule(_) => {}
        }
    }

    diags
}

fn check_cardinality(card: &Cardinality, span: Option<Span>, diags: &mut Vec<Diagnostic>) {
    if let Cardinality::Range { min, max: Some(max), .. } = card {
        if min > max {
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
}

fn kind_label(kind: &SymbolKind) -> &'static str {
    match kind {
        SymbolKind::Concept => "concept",
        SymbolKind::Property => "property",
        SymbolKind::Rule => "rule",
        SymbolKind::Prefix => "prefix",
        SymbolKind::Individual { .. } => "individual",
    }
}
