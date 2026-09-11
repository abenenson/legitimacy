use std::collections::{BTreeMap, BTreeSet};
use std::path::{Component, Path, PathBuf};

use sha2::{Digest, Sha256};
use std::sync::{Mutex, OnceLock};
use syn::parse::{Parse, ParseStream, Parser};
use syn::punctuated::Punctuated;
use syn::visit::Visit;
use syn::{Attribute, Item, Lit, Meta, Token};

const CAPABILITY_ERROR: &str = "capability-shape";

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct ModuleEdge {
    pub(super) from: String,
    pub(super) to: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ActiveModuleGraph {
    module_files: BTreeSet<String>,
    embedded_data: BTreeSet<String>,
    module_edges: Vec<ModuleEdge>,
    inline_modules: BTreeSet<(String, String)>,
    include_owners: BTreeSet<String>,
}

impl ActiveModuleGraph {
    pub(super) fn module_files(&self) -> &BTreeSet<String> {
        &self.module_files
    }

    pub(super) fn embedded_data(&self) -> &BTreeSet<String> {
        &self.embedded_data
    }

    pub(super) fn module_edges(&self) -> &[ModuleEdge] {
        &self.module_edges
    }

    pub(super) fn incoming_count(&self, path: &str) -> usize {
        self.module_edges
            .iter()
            .filter(|edge| edge.to == path)
            .count()
    }

    pub(super) fn owner_subtree_is_singleton(&self, owner: &str) -> bool {
        !self.module_edges.iter().any(|edge| edge.from == owner)
            && !self.inline_modules.iter().any(|(path, _)| path == owner)
            && !self.include_owners.contains(owner)
    }
}

#[derive(Clone, Debug)]
pub(super) struct SelectedCfg {
    profile_test: bool,
    features: BTreeSet<String>,
}

impl SelectedCfg {
    pub(super) fn new(profile_test: bool, features: BTreeSet<String>) -> Self {
        Self {
            profile_test,
            features,
        }
    }

    pub(super) fn profile_test(&self) -> bool {
        self.profile_test
    }

    pub(super) fn features(&self) -> &BTreeSet<String> {
        &self.features
    }
}

pub(super) fn derive_active_library_graph(
    crate_root: &str,
    selected_bytes: &BTreeMap<String, Vec<u8>>,
    cfg: &SelectedCfg,
) -> Result<ActiveModuleGraph, &'static str> {
    let crate_root = normalize_repository_path(Path::new(crate_root))?;
    let root_path = Path::new(&crate_root);
    let module_dir = root_path.parent().ok_or(CAPABILITY_ERROR)?.to_path_buf();
    let mut derivation = GraphDerivation {
        selected_bytes,
        cfg,
        universe_key: selected_bytes
            .keys()
            .cloned()
            .collect::<Vec<_>>()
            .join("\0"),
        graph: ActiveModuleGraph {
            module_files: BTreeSet::new(),
            embedded_data: BTreeSet::new(),
            module_edges: Vec::new(),
            inline_modules: BTreeSet::new(),
            include_owners: BTreeSet::new(),
        },
        visiting: BTreeSet::new(),
    };
    derivation.visit_file(&crate_root, module_dir, true)?;
    Ok(derivation.graph)
}

pub(super) fn visit_active_items(
    file_path: &str,
    source: &str,
    cfg: &SelectedCfg,
    mut visit: impl FnMut(&Item),
) -> Result<(), &'static str> {
    let syntax = syn::parse_file(source).map_err(|_| CAPABILITY_ERROR)?;
    visit_active_item_slice(file_path, &syntax.items, cfg, &mut visit)
}

struct GraphDerivation<'a> {
    selected_bytes: &'a BTreeMap<String, Vec<u8>>,
    cfg: &'a SelectedCfg,
    universe_key: String,
    graph: ActiveModuleGraph,
    visiting: BTreeSet<String>,
}

impl GraphDerivation<'_> {
    fn visit_file(
        &mut self,
        file_path: &str,
        module_dir: PathBuf,
        crate_root: bool,
    ) -> Result<(), &'static str> {
        if !self.graph.module_files.insert(file_path.to_string()) {
            return Ok(());
        }
        if !self.visiting.insert(file_path.to_string()) {
            return Err(CAPABILITY_ERROR);
        }
        let bytes = self.selected_bytes.get(file_path).ok_or(CAPABILITY_ERROR)?;
        let source = std::str::from_utf8(bytes).map_err(|_| CAPABILITY_ERROR)?;
        let context = ModuleContext {
            file_path: file_path.to_string(),
            module_dir,
            inline_path_base: if crate_root {
                Path::new(file_path)
                    .parent()
                    .ok_or(CAPABILITY_ERROR)?
                    .to_path_buf()
            } else {
                inline_path_base(file_path)?
            },
            inline_names: Vec::new(),
        };
        let plan = cached_file_plan(
            source,
            &context,
            self.selected_bytes,
            self.cfg,
            &self.universe_key,
        )?;
        self.graph
            .embedded_data
            .extend(plan.embedded_data.iter().cloned());
        self.graph
            .inline_modules
            .extend(plan.inline_modules.iter().cloned());
        if plan.has_include {
            self.graph.include_owners.insert(file_path.to_string());
        }
        for (edge, child_dir) in plan.module_edges {
            self.graph.module_edges.push(edge.clone());
            self.visit_file(&edge.to, child_dir, false)?;
        }
        self.visiting.remove(file_path);
        Ok(())
    }
}

#[derive(Clone, Debug)]
struct FileGraphPlan {
    module_edges: Vec<(ModuleEdge, PathBuf)>,
    embedded_data: BTreeSet<String>,
    inline_modules: BTreeSet<(String, String)>,
    has_include: bool,
}

struct FilePlanDerivation<'a> {
    selected_bytes: &'a BTreeMap<String, Vec<u8>>,
    cfg: &'a SelectedCfg,
    plan: FileGraphPlan,
}

impl FilePlanDerivation<'_> {
    fn visit_items(&mut self, items: &[Item], context: &ModuleContext) -> Result<(), &'static str> {
        for item in items {
            let attrs = item_attributes(item);
            let edge_sensitive = matches!(item, Item::Mod(_)) || item_has_include_tokens(item);
            if edge_sensitive && !attributes_are_active(attrs, self.cfg)? {
                continue;
            }
            match item {
                Item::Mod(module) => self.visit_module(module, context)?,
                _ => self.visit_embedded_inputs(item, context)?,
            }
        }
        Ok(())
    }

    fn visit_module(
        &mut self,
        module: &syn::ItemMod,
        context: &ModuleContext,
    ) -> Result<(), &'static str> {
        let explicit_path = effective_path_attribute(&module.attrs, self.cfg)?;
        if let Some((_, items)) = &module.content {
            let mut inline_names = context.inline_names.clone();
            inline_names.push(module.ident.to_string());
            self.plan
                .inline_modules
                .insert((context.file_path.clone(), inline_names.join("::")));
            let inline_base = if let Some(path) = explicit_path {
                resolve_relative(
                    Path::new(&context.file_path)
                        .parent()
                        .ok_or(CAPABILITY_ERROR)?,
                    &path,
                )?
            } else {
                context.inline_path_base.join(module.ident.to_string())
            };
            let nested = ModuleContext {
                file_path: context.file_path.clone(),
                module_dir: inline_base.clone(),
                inline_path_base: inline_base,
                inline_names,
            };
            self.visit_items(items, &nested)?;
            return Ok(());
        }

        let target = if let Some(path) = explicit_path {
            let base = if context.inline_names.is_empty() {
                Path::new(&context.file_path)
                    .parent()
                    .ok_or(CAPABILITY_ERROR)?
                    .to_path_buf()
            } else {
                context.inline_path_base.clone()
            };
            resolve_relative(&base, &path)?
        } else {
            resolve_ordinary_module(
                &context.module_dir,
                &module.ident.to_string(),
                self.selected_bytes,
            )?
        };
        let target = normalize_repository_path(&target)?;
        if !self.selected_bytes.contains_key(&target) {
            return Err(CAPABILITY_ERROR);
        }
        let edge = ModuleEdge {
            from: context.file_path.clone(),
            to: target.clone(),
        };
        let child_dir = logical_module_directory(&target)?;
        self.plan.module_edges.push((edge, child_dir));
        Ok(())
    }

    fn visit_embedded_inputs(
        &mut self,
        item: &Item,
        context: &ModuleContext,
    ) -> Result<(), &'static str> {
        let mut visitor = IncludeVisitor { macros: Vec::new() };
        visitor.visit_item(item);
        for invocation in visitor.macros {
            let name = invocation
                .path
                .segments
                .last()
                .map(|segment| segment.ident.to_string())
                .unwrap_or_default();
            let nested_include = IncludeFreeTokens::parse_stream
                .parse2(invocation.tokens.clone())
                .is_err();
            if name == "include" || nested_include {
                self.plan.has_include = true;
                return Err(CAPABILITY_ERROR);
            }
            if name != "include_bytes" && name != "include_str" {
                continue;
            }
            let literal = syn::parse2::<syn::LitStr>(invocation.tokens.clone())
                .map_err(|_| CAPABILITY_ERROR)?;
            let base = Path::new(&context.file_path)
                .parent()
                .ok_or(CAPABILITY_ERROR)?;
            let target = resolve_relative(base, &literal.value())?;
            let target = normalize_repository_path(&target)?;
            if !self.selected_bytes.contains_key(&target) {
                return Err(CAPABILITY_ERROR);
            }
            self.plan.embedded_data.insert(target);
        }
        Ok(())
    }
}

fn cached_file_plan(
    source: &str,
    context: &ModuleContext,
    selected_bytes: &BTreeMap<String, Vec<u8>>,
    cfg: &SelectedCfg,
    universe_key: &str,
) -> Result<FileGraphPlan, &'static str> {
    static CACHE: OnceLock<Mutex<BTreeMap<String, Result<FileGraphPlan, &'static str>>>> =
        OnceLock::new();
    let mut hasher = Sha256::new();
    hasher.update(context.file_path.as_bytes());
    hasher.update(context.module_dir.to_string_lossy().as_bytes());
    hasher.update(context.inline_path_base.to_string_lossy().as_bytes());
    hasher.update([u8::from(cfg.profile_test)]);
    for feature in &cfg.features {
        hasher.update(feature.as_bytes());
        hasher.update([0]);
    }
    hasher.update(universe_key.as_bytes());
    hasher.update(source.as_bytes());
    let key = format!("{:x}", hasher.finalize());
    let cache = CACHE.get_or_init(|| Mutex::new(BTreeMap::new()));
    if let Some(plan) = cache.lock().unwrap().get(&key).cloned() {
        return plan;
    }
    let plan = derive_file_plan(source, context, selected_bytes, cfg);
    cache.lock().unwrap().insert(key, plan.clone());
    plan
}

fn derive_file_plan(
    source: &str,
    context: &ModuleContext,
    selected_bytes: &BTreeMap<String, Vec<u8>>,
    cfg: &SelectedCfg,
) -> Result<FileGraphPlan, &'static str> {
    let syntax = syn::parse_file(source).map_err(|_| CAPABILITY_ERROR)?;
    let mut derivation = FilePlanDerivation {
        selected_bytes,
        cfg,
        plan: FileGraphPlan {
            module_edges: Vec::new(),
            embedded_data: BTreeSet::new(),
            inline_modules: BTreeSet::new(),
            has_include: false,
        },
    };
    derivation.visit_items(&syntax.items, context)?;
    Ok(derivation.plan)
}

#[derive(Clone, Debug)]
struct ModuleContext {
    file_path: String,
    module_dir: PathBuf,
    inline_path_base: PathBuf,
    inline_names: Vec<String>,
}

fn visit_active_item_slice(
    file_path: &str,
    items: &[Item],
    cfg: &SelectedCfg,
    visit: &mut impl FnMut(&Item),
) -> Result<(), &'static str> {
    for item in items {
        let attrs = item_attributes(item);
        let edge_sensitive = matches!(item, Item::Mod(_)) || item_has_include_tokens(item);
        if edge_sensitive && !attributes_are_active(attrs, cfg)? {
            continue;
        }
        visit(item);
        if let Item::Mod(module) = item
            && let Some((_, nested)) = &module.content
        {
            visit_active_item_slice(file_path, nested, cfg, visit)?;
        }
    }
    let _ = file_path;
    Ok(())
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

fn item_has_include_tokens(item: &Item) -> bool {
    let mut visitor = IncludeVisitor { macros: Vec::new() };
    visitor.visit_item(item);
    visitor.macros.into_iter().any(|invocation| {
        let name = invocation
            .path
            .segments
            .last()
            .map(|segment| segment.ident.to_string())
            .unwrap_or_default();
        matches!(name.as_str(), "include" | "include_bytes" | "include_str")
            || IncludeFreeTokens::parse_stream
                .parse2(invocation.tokens.clone())
                .is_err()
    })
}

fn attributes_are_active(attrs: &[Attribute], cfg: &SelectedCfg) -> Result<bool, &'static str> {
    let metas = expanded_attributes(attrs, cfg)?;
    for meta in metas {
        if let Meta::List(list) = &meta
            && list.path.is_ident("cfg")
        {
            let predicate =
                syn::parse2::<Meta>(list.tokens.clone()).map_err(|_| CAPABILITY_ERROR)?;
            if !evaluate_cfg(&predicate, cfg)? {
                return Ok(false);
            }
        }
    }
    Ok(true)
}

fn effective_path_attribute(
    attrs: &[Attribute],
    cfg: &SelectedCfg,
) -> Result<Option<String>, &'static str> {
    let mut paths = Vec::new();
    for meta in expanded_attributes(attrs, cfg)? {
        if let Meta::NameValue(value) = meta
            && value.path.is_ident("path")
        {
            let syn::Expr::Lit(expression) = value.value else {
                return Err(CAPABILITY_ERROR);
            };
            let Lit::Str(path) = expression.lit else {
                return Err(CAPABILITY_ERROR);
            };
            paths.push(path.value());
        }
    }
    match paths.as_slice() {
        [] => Ok(None),
        [path] => Ok(Some(path.clone())),
        _ => Err(CAPABILITY_ERROR),
    }
}

fn expanded_attributes(attrs: &[Attribute], cfg: &SelectedCfg) -> Result<Vec<Meta>, &'static str> {
    let mut expanded = Vec::new();
    for attribute in attrs {
        if selected_linux_inner_cfg(attribute)? {
            continue;
        }
        if !attribute.path().is_ident("cfg_attr") {
            expanded.push(attribute.meta.clone());
            continue;
        }
        let arguments = attribute
            .parse_args::<CfgAttrArguments>()
            .map_err(|_| CAPABILITY_ERROR)?;
        if evaluate_cfg(&arguments.predicate, cfg)? {
            for meta in arguments.attributes {
                expand_meta(meta, cfg, &mut expanded)?;
            }
        }
    }
    Ok(expanded)
}

fn selected_linux_inner_cfg(attribute: &Attribute) -> Result<bool, &'static str> {
    if !matches!(attribute.style, syn::AttrStyle::Inner(_)) {
        return Ok(false);
    }
    let Meta::List(list) = &attribute.meta else {
        return Ok(false);
    };
    if !list.path.is_ident("cfg") {
        return Ok(false);
    }
    let predicate = syn::parse2::<Meta>(list.tokens.clone()).map_err(|_| CAPABILITY_ERROR)?;
    let Meta::NameValue(value) = predicate else {
        return Ok(false);
    };
    let syn::Expr::Lit(expression) = value.value else {
        return Ok(false);
    };
    Ok(value.path.is_ident("target_os")
        && matches!(expression.lit, Lit::Str(target) if target.value() == "linux"))
}

fn expand_meta(
    meta: Meta,
    cfg: &SelectedCfg,
    expanded: &mut Vec<Meta>,
) -> Result<(), &'static str> {
    if let Meta::List(list) = &meta
        && list.path.is_ident("cfg_attr")
    {
        let arguments =
            syn::parse2::<CfgAttrArguments>(list.tokens.clone()).map_err(|_| CAPABILITY_ERROR)?;
        if evaluate_cfg(&arguments.predicate, cfg)? {
            for nested in arguments.attributes {
                expand_meta(nested, cfg, expanded)?;
            }
        }
    } else {
        expanded.push(meta);
    }
    Ok(())
}

fn evaluate_cfg(meta: &Meta, cfg: &SelectedCfg) -> Result<bool, &'static str> {
    match meta {
        Meta::Path(path) if path.is_ident("test") => Ok(cfg.profile_test),
        Meta::NameValue(value) if value.path.is_ident("feature") => {
            let syn::Expr::Lit(expression) = &value.value else {
                return Err(CAPABILITY_ERROR);
            };
            let Lit::Str(feature) = &expression.lit else {
                return Err(CAPABILITY_ERROR);
            };
            Ok(cfg.features.contains(&feature.value()))
        }
        Meta::List(list) if list.path.is_ident("not") => {
            let nested = list
                .parse_args_with(Punctuated::<Meta, Token![,]>::parse_terminated)
                .map_err(|_| CAPABILITY_ERROR)?
                .into_iter()
                .collect::<Vec<_>>();
            if nested.len() != 1 {
                return Err(CAPABILITY_ERROR);
            }
            Ok(!evaluate_cfg(&nested[0], cfg)?)
        }
        Meta::List(list) if list.path.is_ident("all") => {
            let nested = list
                .parse_args_with(Punctuated::<Meta, Token![,]>::parse_terminated)
                .map_err(|_| CAPABILITY_ERROR)?;
            for predicate in nested {
                if !evaluate_cfg(&predicate, cfg)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        Meta::List(list) if list.path.is_ident("any") => {
            let nested = list
                .parse_args_with(Punctuated::<Meta, Token![,]>::parse_terminated)
                .map_err(|_| CAPABILITY_ERROR)?;
            for predicate in nested {
                if evaluate_cfg(&predicate, cfg)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        _ => Err(CAPABILITY_ERROR),
    }
}

struct CfgAttrArguments {
    predicate: Meta,
    attributes: Punctuated<Meta, Token![,]>,
}

impl Parse for CfgAttrArguments {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let predicate = input.parse()?;
        input.parse::<Token![,]>()?;
        let attributes = Punctuated::parse_terminated(input)?;
        Ok(Self {
            predicate,
            attributes,
        })
    }
}

struct IncludeVisitor<'ast> {
    macros: Vec<&'ast syn::Macro>,
}

impl<'ast> Visit<'ast> for IncludeVisitor<'ast> {
    fn visit_macro(&mut self, invocation: &'ast syn::Macro) {
        self.macros.push(invocation);
        syn::visit::visit_macro(self, invocation);
    }
}

struct IncludeFreeTokens;

impl IncludeFreeTokens {
    fn parse_stream(input: ParseStream<'_>) -> syn::Result<Self> {
        input.parse()
    }
}

impl Parse for IncludeFreeTokens {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        while !input.is_empty() {
            if input.peek(syn::Ident) {
                let ident: syn::Ident = input.parse()?;
                if matches!(
                    ident.to_string().as_str(),
                    "include" | "include_bytes" | "include_str"
                ) && input.peek(Token![!])
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

fn resolve_ordinary_module(
    base: &Path,
    name: &str,
    selected_bytes: &BTreeMap<String, Vec<u8>>,
) -> Result<PathBuf, &'static str> {
    let flat = base.join(format!("{name}.rs"));
    let directory = base.join(name).join("mod.rs");
    let flat_name = normalize_repository_path(&flat)?;
    let directory_name = normalize_repository_path(&directory)?;
    match (
        selected_bytes.contains_key(&flat_name),
        selected_bytes.contains_key(&directory_name),
    ) {
        (true, false) => Ok(flat),
        (false, true) => Ok(directory),
        _ => Err(CAPABILITY_ERROR),
    }
}

fn logical_module_directory(path: &str) -> Result<PathBuf, &'static str> {
    let path = Path::new(path);
    let parent = path.parent().ok_or(CAPABILITY_ERROR)?;
    if path.file_name().and_then(|name| name.to_str()) == Some("mod.rs") {
        Ok(parent.to_path_buf())
    } else {
        let stem = path.file_stem().ok_or(CAPABILITY_ERROR)?;
        Ok(parent.join(stem))
    }
}

fn inline_path_base(path: &str) -> Result<PathBuf, &'static str> {
    logical_module_directory(path)
}

fn resolve_relative(base: &Path, literal: &str) -> Result<PathBuf, &'static str> {
    let literal = Path::new(literal);
    if literal.is_absolute() {
        return Err(CAPABILITY_ERROR);
    }
    let path = base.join(literal);
    normalize_repository_path(&path).map(PathBuf::from)
}

pub(super) fn normalize_repository_path(path: &Path) -> Result<String, &'static str> {
    let mut components = Vec::new();
    for component in path.components() {
        match component {
            Component::Normal(value) => components.push(value.to_owned()),
            Component::CurDir => {}
            Component::ParentDir => {
                if components.pop().is_none() {
                    return Err(CAPABILITY_ERROR);
                }
            }
            Component::RootDir | Component::Prefix(_) => return Err(CAPABILITY_ERROR),
        }
    }
    if components.is_empty() {
        return Err(CAPABILITY_ERROR);
    }
    Ok(components
        .iter()
        .collect::<PathBuf>()
        .to_string_lossy()
        .replace('\\', "/"))
}
