//! Symbol index — the single source of truth for what names exist in the
//! workspace.
//!
//! The index is *multi-file aware*: each file contributes its own symbols
//! which are merged into a global lookup table.  Files can be added, updated,
//! or removed independently, making the index suitable for incremental updates
//! as the user edits files.
//!
//! For single-file usage see [`SymbolIndex::from_file`].

use std::collections::HashMap;
use std::sync::Arc;

use dolfin_units::Dimensions;
use rowl::{ConceptDef, Declaration, FactDef, OntologyFile, PrefixDecl, PropertyDef, QualifiedName, QueryDef, RuleDef, TypeRef, UnitDef, error::Span};
use rowl::comment::{Comment, CommentMap};

use crate::infer::TypeIndex;

// ── Symbol kind ──────────────────────────────────────────────────────────────

/// What kind of entity a symbol represents.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymbolKind {
    Concept,
    Property,
    Rule,
    Query,
    Prefix,
    /// A named individual declared in a concept's 'one of:' block.
    Individual {
        parent: String,
    },
    /// A fact (ABox instance) declaration.
    FactInstance,
}

// ── Symbol ───────────────────────────────────────────────────────────────────

/// A fully resolved symbol entry inside the index.
#[derive(Debug, Clone)]
pub struct Symbol {
    /// The canonical name as it appears in source.
    pub name: String,
    pub kind: SymbolKind,
    /// Span of the *definition* site (not a reference).
    pub definition_span: Option<Span>,
    /// Short human-readable description (used for hover / completion).
    pub detail: String,
    /// Source file path or URI this symbol originated from.
    /// `None` for symbols added without a file path (e.g. in tests).
    pub file: Option<String>,
    /// For a `Property` symbol whose declared range is a well-known physical
    /// dimension (its type ref's last name segment matches
    /// `dolfin_units::named_dimension`, e.g. `has weight: unit.Mass`) — the
    /// dimension a `quantity(...)` value assigned to it must have.
    pub dimension: Option<Dimensions>,
}

// ── Per-file symbols ──────────────────────────────────────────────────────────

/// All symbols declared in a single file.
#[derive(Debug, Default, Clone)]
struct FileSymbols {
    symbols: HashMap<String, Symbol>,
    /// `unitdef` declarations; project-wide, see [`SymbolIndex::units`].
    units: Vec<UnitDef>,
    /// The file's prefixes, concepts and properties: what
    /// [`SymbolIndex::type_index`] needs (shared, so cloning the index is cheap).
    schema: Option<Arc<OntologyFile>>,
    /// The file's comments, for descriptions shown outside it (hover on a
    /// reference in another file). Empty when indexed without comments.
    comments: Arc<CommentMap>,
}

impl FileSymbols {
    fn from_ontology(file: &OntologyFile, path: Option<&str>) -> Self {
        let mut fs = FileSymbols {
            schema: Some(Arc::new(OntologyFile {
                declarations: file
                    .declarations
                    .iter()
                    .filter(|d| matches!(d, Declaration::Concept(_) | Declaration::Property(_)))
                    .cloned()
                    .collect(),
                iri_name: None,
                prefixes: file.prefixes.clone(),
                locale: None,
                timezone: None,
                span: None,
            })),
            ..FileSymbols::default()
        };
        for prefix in &file.prefixes {
            fs.insert_prefix(prefix, path);
        }
        for decl in &file.declarations {
            match decl {
                Declaration::Concept(c) => fs.insert_concept(c, path),
                Declaration::Property(p) => fs.insert_property(p, path),
                Declaration::Rule(r) => fs.insert_rule(r, path),
                Declaration::Query(q) => fs.insert_query(q, path),
                Declaration::Fact(f) => fs.insert_fact(f, path),
                // Unit declarations feed a separate project-wide unit registry
                // (see `crate::units`), not the concept/property symbol map.
                Declaration::Unit(u) => fs.units.push(u.clone()),
            }
        }
        fs
    }

    fn insert(&mut self, sym: Symbol) {
        self.symbols.insert(sym.name.clone(), sym);
    }

    fn insert_prefix(&mut self, prefix: &PrefixDecl, path: Option<&str>) {
        self.insert(Symbol {
            name: prefix.alias.clone(),
            kind: SymbolKind::Prefix,
            definition_span: prefix.span,
            detail: format!("prefix {} → {}", prefix.alias, prefix.path),
            file: path.map(str::to_owned),
            dimension: None,
        });
    }

    fn insert_concept(&mut self, c: &ConceptDef, path: Option<&str>) {
        let parents: Vec<String> = c.parents.iter().map(|p| p.to_string()).collect();
        let detail = if parents.is_empty() {
            format!("concept {}", c.name.get())
        } else {
            format!("concept {} sub {}", c.name.get(), parents.join(", "))
        };
        self.insert(Symbol {
            name: c.name.get().clone(),
            kind: SymbolKind::Concept,
            definition_span: c.span,
            detail,
            file: path.map(str::to_owned),
            dimension: None,
        });
        if let Some(variants) = &c.one_of {
            for variant in variants {
                self.insert(Symbol {
                    name: variant.name.clone(),
                    kind: SymbolKind::Individual {
                        parent: c.name.get().clone(),
                    },
                    definition_span: variant.name_span.or(variant.span),
                    detail: format!("individual {} of {}", variant.name, c.name.get()),
                    file: path.map(str::to_owned),
                    dimension: None,
                });
            }
        }
        // Properties declared inline in a concept's `has` block are real
        // properties too — index them so references in queries/rules/facts
        // (S004) don't see them as unknown. A top-level `property` decl with
        // the same name wins (richer detail), so don't clobber an existing one.
        for has in &c.has_declarations {
            if self.symbols.contains_key(&has.name) {
                continue;
            }
            self.insert(Symbol {
                name: has.name.clone(),
                kind: SymbolKind::Property,
                definition_span: has.span,
                detail: format!(
                    "property {} of {}: {}",
                    has.name,
                    c.name.get(),
                    has.type_ref
                ),
                file: path.map(str::to_owned),
                dimension: dimension_of(&has.type_ref),
            });
        }
    }

    fn insert_property(&mut self, p: &PropertyDef, path: Option<&str>) {
        self.insert(Symbol {
            name: p.name.get().clone(),
            kind: SymbolKind::Property,
            definition_span: p.span,
            detail: format!("property {}: {} → {}", p.name.get(), p.domain, p.range),
            file: path.map(str::to_owned),
            dimension: dimension_of(&p.range),
        });
    }

    fn insert_rule(&mut self, r: &RuleDef, path: Option<&str>) {
        self.insert(Symbol {
            name: r.name.clone(),
            kind: SymbolKind::Rule,
            definition_span: r.span,
            detail: format!("rule {}", r.name),
            file: path.map(str::to_owned),
            dimension: None,
        });
    }

    fn insert_query(&mut self, q: &QueryDef, path: Option<&str>) {
        self.insert(Symbol {
            name: q.name.clone(),
            kind: SymbolKind::Query,
            definition_span: q.span,
            detail: format!("query {}", q.name),
            file: path.map(str::to_owned),
            dimension: None,
        });
    }

    fn insert_fact(&mut self, f: &FactDef, path: Option<&str>) {
        let type_names: Vec<String> = f.types.iter().map(|t| t.full()).collect();
        let detail = if type_names.is_empty() {
            format!("fact {}", f.id)
        } else {
            format!("fact {} a {}", f.id, type_names.join(", "))
        };
        self.insert(Symbol {
            name: f.id.clone(),
            kind: SymbolKind::FactInstance,
            definition_span: f.span,
            detail,
            file: path.map(str::to_owned),
            dimension: None,
        });
    }
}

/// If `type_ref` is a named reference whose last name segment matches a
/// well-known physical dimension (`unit.Mass`, `Speed`, …), the dimension it
/// denotes.
fn dimension_of(type_ref: &TypeRef) -> Option<Dimensions> {
    let TypeRef::Named { name, .. } = type_ref else {
        return None;
    };
    dolfin_units::named_dimension(&name.last())
}

// ── SymbolIndex ───────────────────────────────────────────────────────────────

/// Cross-file symbol index.  Supports incremental add / remove of files.
#[derive(Debug, Default, Clone)]
pub struct SymbolIndex {
    /// Per-file symbol maps, keyed by the file path/URI string.
    by_file: HashMap<String, FileSymbols>,
    /// Merged global view for fast single-lookup resolution.
    /// When the same name exists in multiple files the last writer wins
    /// (deterministic within a single `add_file` call).
    global: HashMap<String, Symbol>,
}

impl SymbolIndex {
    // ── Constructors ─────────────────────────────────────────────────────────

    /// Build an index from a single parsed file (no path recorded).
    pub fn from_file(file: &OntologyFile) -> Self {
        let mut idx = SymbolIndex::default();
        idx.add_file("", file);
        idx
    }

    // ── Mutation ─────────────────────────────────────────────────────────────

    /// Index (or re-index) an ontology file under the given `path`.
    ///
    /// If the file was previously indexed under the same path its old symbols
    /// are removed first.
    ///
    /// Cross-file qualified names (`<stem>.<Name>`) are also registered so
    /// that `there.Far` resolves when `Far` is declared in `there.dlf`.
    pub fn add_file(&mut self, path: &str, file: &OntologyFile) {
        self.remove_file(path);
        let mut fs = FileSymbols::from_ontology(file, Some(path));

        // Derive the file stem (e.g. "there" from "/path/to/there.dlf" or
        // "file:///path/to/there.dlf") and add `<stem>.<Name>` aliases so
        // qualified cross-file references resolve.
        if let Some(stem) = file_stem(path) {
            let qualified: Vec<Symbol> = fs
                .symbols
                .values()
                .filter(|s| !matches!(s.kind, SymbolKind::Prefix) && !s.name.contains('.'))
                .map(|s| Symbol {
                    name: format!("{}.{}", stem, s.name),
                    ..s.clone()
                })
                .collect();
            for sym in qualified {
                fs.insert(sym);
            }
        }

        for sym in fs.symbols.values() {
            self.global.insert(sym.name.clone(), sym.clone());
        }
        self.by_file.insert(path.to_owned(), fs);
    }

    /// [`add_file`](Self::add_file), keeping `comments` so the leading
    /// comments of its declarations can be read from other files.
    pub fn add_file_with_comments(&mut self, path: &str, file: &OntologyFile, comments: CommentMap) {
        self.add_file(path, file);
        if let Some(fs) = self.by_file.get_mut(path) {
            fs.comments = Arc::new(comments);
        }
    }

    /// Remove all symbols that originated from `path`.
    pub fn remove_file(&mut self, path: &str) {
        if let Some(fs) = self.by_file.remove(path) {
            for name in fs.symbols.keys() {
                // Only remove from global if no other file re-defines it.
                let still_elsewhere = self
                    .by_file
                    .values()
                    .any(|other| other.symbols.contains_key(name));
                if !still_elsewhere {
                    self.global.remove(name);
                }
            }
        }
    }

    // ── Queries ───────────────────────────────────────────────────────────────

    /// Look up a symbol by name in the global (cross-file) scope.
    pub fn get(&self, name: &str) -> Option<&Symbol> {
        self.global.get(name)
    }

    /// Look up a symbol restricted to a single file.
    pub fn get_in_file(&self, path: &str, name: &str) -> Option<&Symbol> {
        self.by_file.get(path)?.symbols.get(name)
    }

    /// Leading comments of the node at `span` in the file `path` (a symbol's
    /// `file`), or in any file when `path` is `None`.
    pub fn leading_comments(&self, path: Option<&str>, span: Span) -> &[Comment] {
        match path {
            Some(path) => self.by_file.get(path).map(|fs| fs.comments.leading_comments(&span)),
            None => self.by_file.values().map(|fs| fs.comments.leading_comments(&span)).find(|c| !c.is_empty()),
        }
        .unwrap_or(&[])
    }

    /// Every `unitdef` declaration across all indexed files.
    pub fn units(&self) -> impl Iterator<Item = &UnitDef> {
        self.by_file.values().flat_map(|fs| fs.units.iter())
    }

    /// Type-inference view (hierarchy, inherited cardinalities) of every
    /// indexed file, each under its file stem as namespace.
    /// ponytail: rebuilt per call, O(package schema); cache it next to
    /// `global` if it shows up in profiles.
    pub fn type_index(&self) -> TypeIndex {
        let files: Vec<(QualifiedName, &OntologyFile)> = self
            .by_file
            .iter()
            .filter_map(|(path, fs)| {
                let parts = file_stem(path).into_iter().collect();
                Some((QualifiedName::new(parts, None), fs.schema.as_deref()?))
            })
            .collect();
        TypeIndex::build(files.iter().map(|(ns, f)| (ns, *f)))
    }

    /// Iterate all symbols across all files.
    pub fn iter(&self) -> impl Iterator<Item = &Symbol> {
        self.global.values()
    }

    /// Iterate symbols declared in a specific file.
    pub fn iter_file(&self, path: &str) -> impl Iterator<Item = &Symbol> {
        self.by_file
            .get(path)
            .into_iter()
            .flat_map(|fs| fs.symbols.values())
    }

    /// Returns `true` if `name` resolves to a concept (i.e. a type).
    pub fn is_type(&self, name: &str) -> bool {
        matches!(
            self.global.get(name).map(|s| &s.kind),
            Some(SymbolKind::Concept)
        )
    }

    /// All names that are valid types (concepts).
    pub fn type_names(&self) -> Vec<&str> {
        self.global
            .values()
            .filter(|s| s.kind == SymbolKind::Concept)
            .map(|s| s.name.as_str())
            .collect()
    }

    /// All names that are valid concepts.
    pub fn concept_names(&self) -> Vec<&str> {
        self.global
            .values()
            .filter(|s| s.kind == SymbolKind::Concept)
            .map(|s| s.name.as_str())
            .collect()
    }

    /// All names that are valid properties.
    pub fn property_names(&self) -> Vec<&str> {
        self.global
            .values()
            .filter(|s| s.kind == SymbolKind::Property)
            .map(|s| s.name.as_str())
            .collect()
    }
}

// ── Helpers ───────────────────────────────────────────────────────────────────

/// Extract the file stem from a path or `file://` URI.
///
/// `"/path/to/there.dlf"` → `Some("there")`
/// `"file:///path/to/there.dlf"` → `Some("there")`
fn file_stem(path: &str) -> Option<String> {
    let stripped = path.strip_prefix("file://").unwrap_or(path);
    std::path::Path::new(stripped)
        .file_stem()
        .and_then(|s| s.to_str())
        .map(|s| s.to_lowercase())
}
