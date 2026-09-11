use super::direct_graph::{DirectModuleGraph, LogicalModuleId, TargetRole};
use sha2::{Digest, Sha256};
use std::collections::BTreeSet;
use syn::visit::Visit;

const EXPANDED_BYTE_CAP: usize = 16 * 1024 * 1024;
const EXPANDED_NODE_CAP: u64 = 2_000_000;
const AST_DEPTH_CAP: u32 = 128;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SyntaxMeasureFailure {
    Unsupported,
    Cap,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ExpansionFailure {
    UnsupportedExpansionForm,
    ExpansionEvidence,
    ExpansionDependentSourceEdge,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ExpandedTopology {
    pub(crate) target: TargetRole,
    pub(crate) byte_len: u64,
    pub(crate) digest: [u8; 32],
    pub(crate) node_count: u64,
    pub(crate) maximum_depth: u32,
    pub(crate) traversal: Vec<LogicalModuleId>,
    pub(crate) logical_modules: BTreeSet<LogicalModuleId>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ExpandedTargetTopologies {
    pub(crate) library: ExpandedTopology,
    pub(crate) binary: ExpandedTopology,
}

pub(crate) fn parse_expanded_topology(
    target: TargetRole,
    bytes: &[u8],
) -> Result<ExpandedTopology, ExpansionFailure> {
    if bytes.len() > EXPANDED_BYTE_CAP {
        return Err(ExpansionFailure::ExpansionEvidence);
    }
    let source =
        std::str::from_utf8(bytes).map_err(|_| ExpansionFailure::UnsupportedExpansionForm)?;
    let syntax = syn::parse_file(source).map_err(|_| ExpansionFailure::UnsupportedExpansionForm)?;
    let (node_count, maximum_depth) = measure_syntax(&syntax, EXPANDED_NODE_CAP, AST_DEPTH_CAP)
        .map_err(|failure| match failure {
            SyntaxMeasureFailure::Unsupported => ExpansionFailure::UnsupportedExpansionForm,
            SyntaxMeasureFailure::Cap => ExpansionFailure::ExpansionEvidence,
        })?;
    let mut traversal = vec![LogicalModuleId(Vec::new())];
    collect_modules(&syntax.items, &LogicalModuleId(Vec::new()), &mut traversal)?;
    if traversal.len() > 512 {
        return Err(ExpansionFailure::ExpansionEvidence);
    }
    let logical_modules = traversal.iter().cloned().collect::<BTreeSet<_>>();
    if logical_modules.len() != traversal.len() {
        return Err(ExpansionFailure::UnsupportedExpansionForm);
    }
    Ok(ExpandedTopology {
        target,
        byte_len: bytes.len() as u64,
        digest: Sha256::digest(bytes).into(),
        node_count,
        maximum_depth,
        traversal,
        logical_modules,
    })
}

pub(crate) fn measure_syntax(
    syntax: &syn::File,
    node_cap: u64,
    depth_cap: u32,
) -> Result<(u64, u32), SyntaxMeasureFailure> {
    let mut counter = BoundedAstVisitor {
        node_count: 0,
        depth: 0,
        maximum_depth: 0,
        node_cap,
        depth_cap,
        failure: None,
    };
    counter.visit_file(syntax);
    if let Some(failure) = counter.failure {
        Err(failure)
    } else {
        Ok((counter.node_count, counter.maximum_depth))
    }
}

pub(crate) fn reconcile_expanded_topology(
    direct: &DirectModuleGraph,
    expanded: &ExpandedTopology,
) -> Result<(), ExpansionFailure> {
    if direct.target() != expanded.target {
        return Err(ExpansionFailure::ExpansionEvidence);
    }
    let direct_ids = direct.modules().keys().cloned().collect::<BTreeSet<_>>();
    if direct_ids
        .iter()
        .any(|identity| !expanded.logical_modules.contains(identity))
    {
        return Err(ExpansionFailure::ExpansionEvidence);
    }
    if expanded
        .logical_modules
        .iter()
        .any(|identity| !direct_ids.contains(identity))
    {
        return Err(ExpansionFailure::ExpansionDependentSourceEdge);
    }
    Ok(())
}

fn collect_modules(
    items: &[syn::Item],
    parent: &LogicalModuleId,
    traversal: &mut Vec<LogicalModuleId>,
) -> Result<(), ExpansionFailure> {
    for item in items {
        if let syn::Item::Mod(module) = item {
            let Some((_, nested)) = &module.content else {
                return Err(ExpansionFailure::UnsupportedExpansionForm);
            };
            let mut logical = parent.clone();
            logical.0.push(normalize_ident(&module.ident));
            traversal.push(logical.clone());
            collect_modules(nested, &logical, traversal)?;
        }
    }
    Ok(())
}

struct BoundedAstVisitor {
    node_count: u64,
    depth: u32,
    maximum_depth: u32,
    node_cap: u64,
    depth_cap: u32,
    failure: Option<SyntaxMeasureFailure>,
}

impl BoundedAstVisitor {
    fn enter(&mut self) -> bool {
        let Some(nodes) = self.node_count.checked_add(1) else {
            self.failure = Some(SyntaxMeasureFailure::Cap);
            return false;
        };
        let Some(depth) = self.depth.checked_add(1) else {
            self.failure = Some(SyntaxMeasureFailure::Cap);
            return false;
        };
        self.node_count = nodes;
        self.depth = depth;
        self.maximum_depth = self.maximum_depth.max(depth);
        if nodes > self.node_cap || depth > self.depth_cap {
            self.failure = Some(SyntaxMeasureFailure::Cap);
            return false;
        }
        true
    }

    fn leave(&mut self) {
        self.depth -= 1;
    }
}

impl<'ast> Visit<'ast> for BoundedAstVisitor {
    fn visit_item(&mut self, item: &'ast syn::Item) {
        if self.failure.is_some() || !self.enter() {
            return;
        }
        if matches!(item, syn::Item::Verbatim(_)) {
            self.failure = Some(SyntaxMeasureFailure::Unsupported);
        } else {
            syn::visit::visit_item(self, item);
        }
        self.leave();
    }

    fn visit_expr(&mut self, expression: &'ast syn::Expr) {
        if self.failure.is_some() || !self.enter() {
            return;
        }
        if matches!(expression, syn::Expr::Verbatim(_)) {
            self.failure = Some(SyntaxMeasureFailure::Unsupported);
        } else {
            syn::visit::visit_expr(self, expression);
        }
        self.leave();
    }

    fn visit_type(&mut self, ty: &'ast syn::Type) {
        if self.failure.is_some() || !self.enter() {
            return;
        }
        if matches!(ty, syn::Type::Verbatim(_)) {
            self.failure = Some(SyntaxMeasureFailure::Unsupported);
        } else {
            syn::visit::visit_type(self, ty);
        }
        self.leave();
    }

    fn visit_pat(&mut self, pattern: &'ast syn::Pat) {
        if self.failure.is_some() || !self.enter() {
            return;
        }
        if matches!(pattern, syn::Pat::Verbatim(_)) {
            self.failure = Some(SyntaxMeasureFailure::Unsupported);
        } else {
            syn::visit::visit_pat(self, pattern);
        }
        self.leave();
    }

    fn visit_stmt(&mut self, statement: &'ast syn::Stmt) {
        if self.failure.is_some() || !self.enter() {
            return;
        }
        syn::visit::visit_stmt(self, statement);
        self.leave();
    }

    fn visit_attribute(&mut self, attribute: &'ast syn::Attribute) {
        if self.failure.is_some() || !self.enter() {
            return;
        }
        syn::visit::visit_attribute(self, attribute);
        self.leave();
    }

    fn visit_macro(&mut self, invocation: &'ast syn::Macro) {
        if self.failure.is_some() || !self.enter() {
            return;
        }
        syn::visit::visit_macro(self, invocation);
        self.leave();
    }
}

fn normalize_ident(ident: &syn::Ident) -> String {
    let value = ident.to_string();
    value.strip_prefix("r#").unwrap_or(&value).to_string()
}

pub(crate) fn assert_expanded_topology_fixture_is_whole_stream_and_target_separate() {
    let active = super::selected_cfg::ActiveCfgAtoms::parse(b"target_os=\"linux\"\n").unwrap();
    let grammar = super::selected_cfg::RecognizedCfgGrammar::parse(
        b"cfg(target_os, values(\"linux\", \"windows\"))\n",
    )
    .unwrap();
    let table = std::collections::BTreeMap::from([
        (
            "lib/root.source".to_string(),
            b"#[path=\"child.source\"] mod child;\n".to_vec(),
        ),
        (
            "lib/child.source".to_string(),
            b"mod nested { pub fn value() {} }\n".to_vec(),
        ),
        ("bin/root.source".to_string(), b"fn main() {}\n".to_vec()),
    ]);
    let direct = super::direct_graph::derive_target_graphs(
        "lib/root.source",
        "bin/root.source",
        &table,
        (&active, &grammar),
        (&active, &grammar),
    )
    .unwrap();
    let library = parse_expanded_topology(
        TargetRole::Library,
        b"mod child { mod nested { pub fn value() {} } }\n",
    )
    .unwrap();
    let binary = parse_expanded_topology(TargetRole::Binary, b"fn main() {}\n").unwrap();
    assert_eq!(
        ExpandedTargetTopologies {
            library: library.clone(),
            binary: binary.clone(),
        }
        .library
        .target,
        TargetRole::Library
    );
    assert_eq!(
        reconcile_expanded_topology(&direct.library, &library),
        Ok(())
    );
    assert_eq!(reconcile_expanded_topology(&direct.binary, &binary), Ok(()));

    let missing = parse_expanded_topology(TargetRole::Library, b"mod child {}\n").unwrap();
    assert_eq!(
        reconcile_expanded_topology(&direct.library, &missing),
        Err(ExpansionFailure::ExpansionEvidence)
    );
    let generated = parse_expanded_topology(
        TargetRole::Binary,
        b"mod generated { pub fn value() {} }\nfn main() {}\n",
    )
    .unwrap();
    assert_eq!(
        reconcile_expanded_topology(&direct.binary, &generated),
        Err(ExpansionFailure::ExpansionDependentSourceEdge)
    );
    assert_eq!(library.byte_len, 47);
    assert!(library.node_count >= library.logical_modules.len() as u64);
    assert!(library.maximum_depth > 1);
}
