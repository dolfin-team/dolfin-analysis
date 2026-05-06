//! Hover information: given a byte offset into source, return a markdown
//! string describing the symbol under the cursor.

use rowl::{
    Declaration, OntologyFile, TypeRef,
    error::{Location, Span},
};

use crate::symbols::SymbolTable;

/// Attempt to find a meaningful hover string for the given source position.
///
/// Returns `None` when the cursor is not over a recognised identifier.
pub fn hover_at(
    file: &OntologyFile,
    table: &SymbolTable,
    position: Location,
) -> Option<String> {
    // Walk declarations to find a span that contains the position, then
    // return the corresponding symbol detail.
    for decl in &file.declarations {
        if let Some(text) = hover_in_decl(decl, table, position) {
            return Some(text);
        }
    }
    None
}

fn hover_in_decl(
    decl: &Declaration,
    table: &SymbolTable,
    pos: Location,
) -> Option<String> {
    match decl {
        Declaration::Concept(c) => {
            // Check if cursor is on the concept name itself.
            if span_contains(c.span, pos) {
                return table.get(&c.name).map(|s| markdown_symbol(s));
            }
            // Check parent type references.
            for parent in &c.parents {
                if let Some(t) = hover_type_ref(parent, table, pos) {
                    return Some(t);
                }
            }
            // Check has declarations.
            for has in &c.has_declarations {
                if span_contains(has.span, pos) {
                    if let Some(sym) = table.get(&has.name) {
                        return Some(markdown_symbol(sym));
                    }
                }
                if let Some(t) = hover_type_ref(&has.type_ref, table, pos) {
                    return Some(t);
                }
            }
            None
        }
        Declaration::Property(p) => {
            if span_contains(p.span, pos) {
                return table.get(&p.name).map(|s| markdown_symbol(s));
            }
            hover_type_ref(&p.domain, table, pos)
                .or_else(|| hover_type_ref(&p.range, table, pos))
        }
        Declaration::Rule(r) => {
            if span_contains(r.span, pos) {
                table.get(&r.name).map(|s| markdown_symbol(s))
            } else {
                None
            }
        }
    }
}

fn hover_type_ref(type_ref: &TypeRef, table: &SymbolTable, pos: Location) -> Option<String> {
    match type_ref {
        TypeRef::Named { name, span } => {
            if span_contains(*span, pos) {
                let last = name.last();
                let full = name.full();
                table
                    .get(&last)
                    .or_else(|| table.get(&full))
                    .map(markdown_symbol)
            } else {
                None
            }
        }
        TypeRef::Primitive { span, kind } => {
            if span_contains(*span, pos) {
                Some(format!("```dolfin\nprimitive {:?}\n```", kind))
            } else {
                None
            }
        }
    }
}

fn span_contains(span: Option<Span>, pos: Location) -> bool {
    span.map_or(false, |s| s.start.offset <= pos.offset && pos.offset <= s.end.offset)
}

fn markdown_symbol(sym: &crate::symbols::Symbol) -> String {
    format!("```dolfin\n{}\n```", sym.detail)
}
