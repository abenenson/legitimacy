use super::selected_cfg::{ActiveCfgAtoms, CfgFailure, RecognizedCfgGrammar};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Component, Path, PathBuf};
use syn::parse::{Parse, ParseStream, Parser};
use syn::visit::Visit;
use syn::{Attribute, Item, LitStr, Meta};

const REPOSITORY_PATH_CAP: usize = 4_096;
const ONE_INPUT_BYTE_CAP: usize = 64 * 1024 * 1024;
const DIRECT_FILE_CAP: usize = 256;
const DIRECT_LOGICAL_MODULE_CAP: usize = 512;
const DIRECT_EDGE_CAP: usize = 1_024;
const DIRECT_NODE_CAP: u64 = 1_000_000;
const AST_DEPTH_CAP: u32 = 128;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum TargetRole {
    Library,
    Binary,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct LogicalModuleId(pub(crate) Vec<String>);

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct DirectModuleEdge {
    pub(crate) from: LogicalModuleId,
    pub(crate) to: LogicalModuleId,
    pub(crate) source_path: String,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct EmbeddedDataEdge {
    pub(crate) owner: LogicalModuleId,
    pub(crate) data_path: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DirectModuleGraph {
    target: TargetRole,
    root: String,
    traversal: Vec<LogicalModuleId>,
    modules: BTreeMap<LogicalModuleId, String>,
    edges: Vec<DirectModuleEdge>,
    embedded_data: Vec<EmbeddedDataEdge>,
}

impl DirectModuleGraph {
    pub(crate) fn target(&self) -> TargetRole {
        self.target
    }

    pub(crate) fn root(&self) -> &str {
        &self.root
    }

    pub(crate) fn traversal(&self) -> &[LogicalModuleId] {
        &self.traversal
    }

    pub(crate) fn modules(&self) -> &BTreeMap<LogicalModuleId, String> {
        &self.modules
    }

    pub(crate) fn edges(&self) -> &[DirectModuleEdge] {
        &self.edges
    }

    pub(crate) fn embedded_data(&self) -> &[EmbeddedDataEdge] {
        &self.embedded_data
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DirectTargetGraphs {
    pub(crate) library: DirectModuleGraph,
    pub(crate) binary: DirectModuleGraph,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SemanticModuleSource<'a> {
    pub(crate) source_path: &'a str,
    pub(crate) source: &'a str,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum DirectGraphFailure {
    SelectedInputRead,
    CfgEvidence,
    RecognizedCfgGrammar,
    UnsupportedCfgPredicate,
    UnsupportedExpansionForm,
    DirectModuleGraph,
    SemanticModuleParse,
}

impl From<CfgFailure> for DirectGraphFailure {
    fn from(value: CfgFailure) -> Self {
        match value {
            CfgFailure::CfgEvidence => Self::CfgEvidence,
            CfgFailure::RecognizedCfgGrammar => Self::RecognizedCfgGrammar,
            CfgFailure::UnsupportedCfgPredicate => Self::UnsupportedCfgPredicate,
        }
    }
}

pub(crate) fn derive_target_graphs(
    library_root: &str,
    binary_root: &str,
    selected_bytes: &BTreeMap<String, Vec<u8>>,
    library_cfg: (&ActiveCfgAtoms, &RecognizedCfgGrammar),
    binary_cfg: (&ActiveCfgAtoms, &RecognizedCfgGrammar),
) -> Result<DirectTargetGraphs, DirectGraphFailure> {
    Ok(DirectTargetGraphs {
        library: derive_graph(
            TargetRole::Library,
            library_root,
            selected_bytes,
            library_cfg.0,
            library_cfg.1,
        )?,
        binary: derive_graph(
            TargetRole::Binary,
            binary_root,
            selected_bytes,
            binary_cfg.0,
            binary_cfg.1,
        )?,
    })
}

pub(crate) fn semantic_module_sources<'a>(
    graphs: &'a DirectTargetGraphs,
    selected_bytes: &'a BTreeMap<String, Vec<u8>>,
) -> Result<BTreeMap<(TargetRole, LogicalModuleId), SemanticModuleSource<'a>>, DirectGraphFailure> {
    let mut sources = BTreeMap::new();
    for graph in [&graphs.library, &graphs.binary] {
        for (logical, path) in graph.modules() {
            let bytes = selected_bytes
                .get(path)
                .ok_or(DirectGraphFailure::SelectedInputRead)?;
            let source =
                std::str::from_utf8(bytes).map_err(|_| DirectGraphFailure::SemanticModuleParse)?;
            if syn::parse_file(source).is_err() {
                return Err(DirectGraphFailure::SemanticModuleParse);
            }
            let key = (graph.target(), logical.clone());
            if sources
                .insert(
                    key,
                    SemanticModuleSource {
                        source_path: path,
                        source,
                    },
                )
                .is_some()
            {
                return Err(DirectGraphFailure::DirectModuleGraph);
            }
        }
    }
    Ok(sources)
}

pub(crate) fn derive_graph(
    target: TargetRole,
    root: &str,
    selected_bytes: &BTreeMap<String, Vec<u8>>,
    active: &ActiveCfgAtoms,
    grammar: &RecognizedCfgGrammar,
) -> Result<DirectModuleGraph, DirectGraphFailure> {
    let root = normalize_path(Path::new(root))?;
    let mut derivation = Derivation {
        selected_bytes,
        active,
        grammar,
        graph: DirectModuleGraph {
            target,
            root: root.clone(),
            traversal: Vec::new(),
            modules: BTreeMap::new(),
            edges: Vec::new(),
            embedded_data: Vec::new(),
        },
        active_paths: BTreeSet::new(),
    };
    let parent = Path::new(&root)
        .parent()
        .ok_or(DirectGraphFailure::DirectModuleGraph)?
        .to_path_buf();
    derivation.visit_file(&root, LogicalModuleId(Vec::new()), parent.clone(), parent)?;
    Ok(derivation.graph)
}

struct Derivation<'a> {
    selected_bytes: &'a BTreeMap<String, Vec<u8>>,
    active: &'a ActiveCfgAtoms,
    grammar: &'a RecognizedCfgGrammar,
    graph: DirectModuleGraph,
    active_paths: BTreeSet<String>,
}

#[derive(Clone)]
struct ModuleContext {
    file_path: String,
    logical: LogicalModuleId,
    module_dir: PathBuf,
    inline_path_base: PathBuf,
}

impl Derivation<'_> {
    fn visit_file(
        &mut self,
        file_path: &str,
        logical: LogicalModuleId,
        module_dir: PathBuf,
        inline_path_base: PathBuf,
    ) -> Result<(), DirectGraphFailure> {
        if !self.active_paths.insert(file_path.to_string()) {
            return Err(DirectGraphFailure::DirectModuleGraph);
        }
        if self
            .graph
            .modules
            .insert(logical.clone(), file_path.to_string())
            .is_some()
        {
            return Err(DirectGraphFailure::DirectModuleGraph);
        }
        enforce_graph_caps(&self.graph)?;
        self.graph.traversal.push(logical.clone());
        let bytes = self
            .selected_bytes
            .get(file_path)
            .ok_or(DirectGraphFailure::SelectedInputRead)?;
        if bytes.len() > ONE_INPUT_BYTE_CAP {
            return Err(DirectGraphFailure::SelectedInputRead);
        }
        let source =
            std::str::from_utf8(bytes).map_err(|_| DirectGraphFailure::SemanticModuleParse)?;
        let syntax =
            syn::parse_file(source).map_err(|_| DirectGraphFailure::SemanticModuleParse)?;
        super::selected_expansion::measure_syntax(&syntax, DIRECT_NODE_CAP, AST_DEPTH_CAP)
            .map_err(|failure| match failure {
                super::selected_expansion::SyntaxMeasureFailure::Unsupported => {
                    DirectGraphFailure::UnsupportedExpansionForm
                }
                super::selected_expansion::SyntaxMeasureFailure::Cap => {
                    DirectGraphFailure::DirectModuleGraph
                }
            })?;
        self.visit_items(
            &syntax.items,
            &ModuleContext {
                file_path: file_path.to_string(),
                logical,
                module_dir,
                inline_path_base,
            },
        )?;
        self.active_paths.remove(file_path);
        Ok(())
    }

    fn visit_items(
        &mut self,
        items: &[Item],
        context: &ModuleContext,
    ) -> Result<(), DirectGraphFailure> {
        for item in items {
            let Some(attributes) = self
                .grammar
                .retained_attributes(self.active, item_attributes(item))?
            else {
                continue;
            };
            inspect_attribute_tokens(&attributes)?;
            match item {
                Item::Mod(module) => self.visit_module(module, context, &attributes)?,
                Item::Macro(item_macro) if item_macro.ident.is_some() => {
                    NoIncludeTokens::parse_stream
                        .parse2(item_macro.mac.tokens.clone())
                        .map_err(|_| DirectGraphFailure::UnsupportedExpansionForm)?;
                }
                _ => self.visit_macros(item, context)?,
            }
        }
        Ok(())
    }

    fn visit_module(
        &mut self,
        module: &syn::ItemMod,
        context: &ModuleContext,
        attributes: &[Meta],
    ) -> Result<(), DirectGraphFailure> {
        let name = normalize_ident(&module.ident);
        let mut logical = context.logical.clone();
        logical.0.push(name.clone());
        let path_attribute = exact_path_attribute(attributes)?;
        if let Some((_, items)) = &module.content {
            if self
                .graph
                .modules
                .insert(logical.clone(), context.file_path.clone())
                .is_some()
            {
                return Err(DirectGraphFailure::DirectModuleGraph);
            }
            enforce_graph_caps(&self.graph)?;
            self.graph.traversal.push(logical.clone());
            let inline_base = if let Some(path) = path_attribute {
                resolve_relative(
                    Path::new(&context.file_path)
                        .parent()
                        .ok_or(DirectGraphFailure::DirectModuleGraph)?,
                    &path,
                )?
            } else {
                context.inline_path_base.join(&name)
            };
            self.visit_items(
                items,
                &ModuleContext {
                    file_path: context.file_path.clone(),
                    logical,
                    module_dir: inline_base.clone(),
                    inline_path_base: inline_base,
                },
            )?;
            return Ok(());
        }
        let target = if let Some(path) = path_attribute {
            resolve_relative(
                Path::new(&context.file_path)
                    .parent()
                    .ok_or(DirectGraphFailure::DirectModuleGraph)?,
                &path,
            )?
        } else {
            resolve_ordinary(&context.module_dir, &name, self.selected_bytes)?
        };
        let target = normalize_path(&target)?;
        if !self.selected_bytes.contains_key(&target) {
            return Err(DirectGraphFailure::SelectedInputRead);
        }
        self.graph.edges.push(DirectModuleEdge {
            from: context.logical.clone(),
            to: logical.clone(),
            source_path: target.clone(),
        });
        enforce_graph_caps(&self.graph)?;
        let child_dir = module_directory(&target)?;
        self.visit_file(&target, logical, child_dir.clone(), child_dir)
    }

    fn visit_macros(
        &mut self,
        item: &Item,
        context: &ModuleContext,
    ) -> Result<(), DirectGraphFailure> {
        let mut collector = MacroCollector { macros: Vec::new() };
        collector.visit_item(item);
        for invocation in collector.macros {
            let Some(name) = invocation
                .path
                .segments
                .last()
                .map(|part| part.ident.to_string())
            else {
                continue;
            };
            if !matches!(name.as_str(), "include" | "include_bytes" | "include_str") {
                NoIncludeTokens::parse_stream
                    .parse2(invocation.tokens.clone())
                    .map_err(|_| DirectGraphFailure::UnsupportedExpansionForm)?;
                continue;
            }
            let literal = syn::parse2::<LitStr>(invocation.tokens.clone())
                .map_err(|_| DirectGraphFailure::UnsupportedExpansionForm)?;
            if name == "include" {
                return Err(DirectGraphFailure::UnsupportedExpansionForm);
            }
            let base = Path::new(&context.file_path)
                .parent()
                .ok_or(DirectGraphFailure::DirectModuleGraph)?;
            let data_path = normalize_path(&resolve_relative(base, &literal.value())?)?;
            if !self.selected_bytes.contains_key(&data_path) {
                return Err(DirectGraphFailure::SelectedInputRead);
            }
            self.graph.embedded_data.push(EmbeddedDataEdge {
                owner: context.logical.clone(),
                data_path,
            });
        }
        Ok(())
    }
}

struct MacroCollector<'ast> {
    macros: Vec<&'ast syn::Macro>,
}

impl<'ast> Visit<'ast> for MacroCollector<'ast> {
    fn visit_macro(&mut self, invocation: &'ast syn::Macro) {
        self.macros.push(invocation);
        syn::visit::visit_macro(self, invocation);
    }
}

struct NoIncludeTokens;

impl NoIncludeTokens {
    fn parse_stream(input: ParseStream<'_>) -> syn::Result<Self> {
        input.parse()
    }
}

impl Parse for NoIncludeTokens {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        while !input.is_empty() {
            if input.peek(syn::Ident) {
                let ident: syn::Ident = input.parse()?;
                if matches!(
                    ident.to_string().as_str(),
                    "include" | "include_bytes" | "include_str"
                ) && input.peek(syn::Token![!])
                {
                    return Err(input.error("include-family token"));
                }
                continue;
            }
            if input.peek(syn::token::Paren) {
                let nested;
                syn::parenthesized!(nested in input);
                nested.parse::<Self>()?;
                continue;
            }
            if input.peek(syn::token::Bracket) {
                let nested;
                syn::bracketed!(nested in input);
                nested.parse::<Self>()?;
                continue;
            }
            if input.peek(syn::token::Brace) {
                let nested;
                syn::braced!(nested in input);
                nested.parse::<Self>()?;
                continue;
            }
            input.step(|cursor| {
                cursor
                    .token_tree()
                    .map(|(_, next)| ((), next))
                    .ok_or_else(|| cursor.error("token"))
            })?;
        }
        Ok(Self)
    }
}

fn inspect_attribute_tokens(attributes: &[Meta]) -> Result<(), DirectGraphFailure> {
    for attribute in attributes {
        let tokens = match attribute {
            Meta::Path(_) => continue,
            Meta::List(list) => list.tokens.clone(),
            Meta::NameValue(value) => {
                let syn::Expr::Macro(invocation) = &value.value else {
                    continue;
                };
                invocation.mac.tokens.clone()
            }
        };
        NoIncludeTokens::parse_stream
            .parse2(tokens)
            .map_err(|_| DirectGraphFailure::UnsupportedExpansionForm)?;
    }
    Ok(())
}

fn exact_path_attribute(attributes: &[Meta]) -> Result<Option<String>, DirectGraphFailure> {
    let mut paths = Vec::new();
    for attribute in attributes {
        if let Meta::NameValue(value) = attribute
            && value.path.is_ident("path")
        {
            let syn::Expr::Lit(value) = &value.value else {
                return Err(DirectGraphFailure::DirectModuleGraph);
            };
            let syn::Lit::Str(value) = &value.lit else {
                return Err(DirectGraphFailure::DirectModuleGraph);
            };
            paths.push(value.value());
        }
    }
    match paths.as_slice() {
        [] => Ok(None),
        [path] => Ok(Some(path.clone())),
        _ => Err(DirectGraphFailure::DirectModuleGraph),
    }
}

fn item_attributes(item: &Item) -> &[Attribute] {
    match item {
        Item::Const(item) => &item.attrs,
        Item::Enum(item) => &item.attrs,
        Item::ExternCrate(item) => &item.attrs,
        Item::Fn(item) => &item.attrs,
        Item::ForeignMod(item) => &item.attrs,
        Item::Impl(item) => &item.attrs,
        Item::Macro(item) => &item.attrs,
        Item::Mod(item) => &item.attrs,
        Item::Static(item) => &item.attrs,
        Item::Struct(item) => &item.attrs,
        Item::Trait(item) => &item.attrs,
        Item::TraitAlias(item) => &item.attrs,
        Item::Type(item) => &item.attrs,
        Item::Union(item) => &item.attrs,
        Item::Use(item) => &item.attrs,
        _ => &[],
    }
}

fn resolve_ordinary(
    base: &Path,
    name: &str,
    selected_bytes: &BTreeMap<String, Vec<u8>>,
) -> Result<PathBuf, DirectGraphFailure> {
    let flat = base.join(format!("{name}.rs"));
    let directory = base.join(name).join("mod.rs");
    let flat_key = normalize_path(&flat)?;
    let directory_key = normalize_path(&directory)?;
    match (
        selected_bytes.contains_key(&flat_key),
        selected_bytes.contains_key(&directory_key),
    ) {
        (true, false) => Ok(flat),
        (false, true) => Ok(directory),
        _ => Err(DirectGraphFailure::DirectModuleGraph),
    }
}

fn module_directory(path: &str) -> Result<PathBuf, DirectGraphFailure> {
    let path = Path::new(path);
    let parent = path.parent().ok_or(DirectGraphFailure::DirectModuleGraph)?;
    if path.file_name().and_then(|name| name.to_str()) == Some("mod.rs") {
        Ok(parent.to_path_buf())
    } else {
        Ok(parent.join(
            path.file_stem()
                .ok_or(DirectGraphFailure::DirectModuleGraph)?,
        ))
    }
}

fn resolve_relative(base: &Path, literal: &str) -> Result<PathBuf, DirectGraphFailure> {
    let literal = Path::new(literal);
    if literal.is_absolute() {
        return Err(DirectGraphFailure::DirectModuleGraph);
    }
    let joined = base.join(literal);
    normalize_path(&joined).map(PathBuf::from)
}

fn normalize_path(path: &Path) -> Result<String, DirectGraphFailure> {
    let mut parts = Vec::new();
    for part in path.components() {
        match part {
            Component::Normal(value) => {
                let value = value
                    .to_str()
                    .ok_or(DirectGraphFailure::DirectModuleGraph)?;
                if value.is_empty() || value.contains('\\') || value.contains('\0') {
                    return Err(DirectGraphFailure::DirectModuleGraph);
                }
                parts.push(value.to_string());
            }
            Component::CurDir => {}
            Component::ParentDir => {
                if parts.pop().is_none() {
                    return Err(DirectGraphFailure::DirectModuleGraph);
                }
            }
            Component::RootDir | Component::Prefix(_) => {
                return Err(DirectGraphFailure::DirectModuleGraph);
            }
        }
    }
    if parts.is_empty() {
        return Err(DirectGraphFailure::DirectModuleGraph);
    }
    let normalized = parts.join("/");
    if normalized.len() > REPOSITORY_PATH_CAP {
        return Err(DirectGraphFailure::DirectModuleGraph);
    }
    Ok(normalized)
}

fn enforce_graph_caps(graph: &DirectModuleGraph) -> Result<(), DirectGraphFailure> {
    if graph.modules.len() > DIRECT_LOGICAL_MODULE_CAP
        || graph
            .edges
            .len()
            .checked_add(graph.embedded_data.len())
            .is_none_or(|edges| edges > DIRECT_EDGE_CAP)
        || graph.modules.values().collect::<BTreeSet<_>>().len() > DIRECT_FILE_CAP
    {
        Err(DirectGraphFailure::DirectModuleGraph)
    } else {
        Ok(())
    }
}

fn normalize_ident(ident: &syn::Ident) -> String {
    let value = ident.to_string();
    value.strip_prefix("r#").unwrap_or(&value).to_string()
}

pub(crate) fn assert_direct_graph_parsing_is_suffix_independent_and_fail_closed() {
    let active = ActiveCfgAtoms::parse(b"target_os=\"linux\"\n").unwrap();
    let grammar =
        RecognizedCfgGrammar::parse(b"cfg(target_os, values(\"linux\", \"windows\"))\n").unwrap();
    let bytes = BTreeMap::from([
        (
            "roots/library.entry".to_string(),
            b"#[cfg_attr(target_os = \"linux\", cfg_attr(target_os = \"linux\", path = \"../modules/child.data\"))] mod child;\n".to_vec(),
        ),
        (
            "modules/child.data".to_string(),
            b"#[cfg(target_os = \"windows\")] mod absent;\n\
              mod nested { pub fn retained() {} }\n\
              const DATA: &[u8] = include_bytes!(\"payload.bin\");\n"
                .to_vec(),
        ),
        ("modules/payload.bin".to_string(), vec![0, 1, 2]),
        ("roots/binary.entry".to_string(), b"fn main() {}\n".to_vec()),
    ]);
    let graphs = derive_target_graphs(
        "roots/library.entry",
        "roots/binary.entry",
        &bytes,
        (&active, &grammar),
        (&active, &grammar),
    )
    .unwrap();
    assert_eq!(graphs.library.target(), TargetRole::Library);
    assert_eq!(graphs.binary.target(), TargetRole::Binary);
    assert_eq!(graphs.library.root(), "roots/library.entry");
    assert_eq!(graphs.library.traversal().len(), 3);
    assert_eq!(graphs.library.modules().len(), 3);
    assert_eq!(graphs.library.edges().len(), 1);
    assert_eq!(graphs.library.embedded_data().len(), 1);
    let semantic = semantic_module_sources(&graphs, &bytes).unwrap();
    assert_eq!(semantic.len(), 4);
    assert_eq!(
        semantic[&(TargetRole::Library, LogicalModuleId(vec!["child".into()]))].source_path,
        "modules/child.data"
    );
    assert!(
        semantic
            .values()
            .all(|entry| !entry.source.contains('\u{fffd}'))
    );
    assert_eq!(
        graphs.library.modules()[&LogicalModuleId(vec!["child".into()])],
        "modules/child.data"
    );
    assert_eq!(
        graphs.library.modules()[&LogicalModuleId(vec!["child".into(), "nested".into()])],
        "modules/child.data"
    );

    let mut ambiguous = bytes.clone();
    ambiguous.insert("roots/duplicate.rs".to_string(), b"".to_vec());
    ambiguous.insert("roots/duplicate/mod.rs".to_string(), b"".to_vec());
    ambiguous.insert(
        "roots/binary.entry".to_string(),
        b"mod duplicate;\n".to_vec(),
    );
    assert_eq!(
        derive_graph(
            TargetRole::Binary,
            "roots/binary.entry",
            &ambiguous,
            &active,
            &grammar
        ),
        Err(DirectGraphFailure::DirectModuleGraph)
    );

    let mut constructed = bytes;
    constructed.insert(
        "roots/binary.entry".to_string(),
        b"const DATA: &[u8] = include_bytes!(concat!(\"x\", \".bin\"));\n".to_vec(),
    );
    assert_eq!(
        derive_graph(
            TargetRole::Binary,
            "roots/binary.entry",
            &constructed,
            &active,
            &grammar
        ),
        Err(DirectGraphFailure::UnsupportedExpansionForm)
    );

    let mut hidden = constructed;
    hidden.insert(
        "roots/binary.entry".to_string(),
        b"#[cfg(target_os = \"windows\")]\nconst DATA: &[u8] = include_bytes!(concat!(\"x\", \".bin\"));\nfn main() {}\n".to_vec(),
    );
    assert!(
        derive_graph(
            TargetRole::Binary,
            "roots/binary.entry",
            &hidden,
            &active,
            &grammar
        )
        .is_ok()
    );

    let mut invented = hidden;
    invented.insert(
        "roots/binary.entry".to_string(),
        b"#[cfg(invented_target = \"linux\")] fn main() {}\n".to_vec(),
    );
    assert_eq!(
        derive_graph(
            TargetRole::Binary,
            "roots/binary.entry",
            &invented,
            &active,
            &grammar
        ),
        Err(DirectGraphFailure::UnsupportedCfgPredicate)
    );
}
