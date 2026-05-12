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

use rowl::{ConceptDef, Declaration, OntologyFile, PrefixDecl, PropertyDef, RuleDef, error::Span};

// ── Symbol kind ──────────────────────────────────────────────────────────────

/// What kind of entity a symbol represents.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymbolKind {
    Concept,
    Property,
    Rule,
    Prefix,
    /// A named individual declared in a concept's 'one of:' block.
    Individual {
        parent: String,
    },
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
}

// ── Per-file symbols ──────────────────────────────────────────────────────────

/// All symbols declared in a single file.
#[derive(Debug, Default, Clone)]
struct FileSymbols {
    symbols: HashMap<String, Symbol>,
}

impl FileSymbols {
    fn from_ontology(file: &OntologyFile, path: Option<&str>) -> Self {
        let mut fs = FileSymbols::default();
        for prefix in &file.prefixes {
            fs.insert_prefix(prefix, path);
        }
        for decl in &file.declarations {
            match decl {
                Declaration::Concept(c) => fs.insert_concept(c, path),
                Declaration::Property(p) => fs.insert_property(p, path),
                Declaration::Rule(r) => fs.insert_rule(r, path),
                Declaration::Fact(_) => {}
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
        });
        if let Some(variants) = &c.one_of {
            for variant in variants {
                self.insert(Symbol {
                    name: variant.name.clone(),
                    kind: SymbolKind::Individual {
                        parent: c.name.get().clone(),
                    },
                    definition_span: variant.span,
                    detail: format!("individual {} of {}", variant.name, c.name.get()),
                    file: path.map(str::to_owned),
                });
            }
        }
    }

    fn insert_property(&mut self, p: &PropertyDef, path: Option<&str>) {
        self.insert(Symbol {
            name: p.name.get().clone(),
            kind: SymbolKind::Property,
            definition_span: p.span,
            detail: format!("property {}: {} → {}", p.name.get(), p.domain, p.range),
            file: path.map(str::to_owned),
        });
    }

    fn insert_rule(&mut self, r: &RuleDef, path: Option<&str>) {
        self.insert(Symbol {
            name: r.name.clone(),
            kind: SymbolKind::Rule,
            definition_span: r.span,
            detail: format!("rule {}", r.name),
            file: path.map(str::to_owned),
        });
    }
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
