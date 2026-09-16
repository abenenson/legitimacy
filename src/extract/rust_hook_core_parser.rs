mod source_spans;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use source_spans::RustHookCoreSpanIndex;
use std::{collections::BTreeSet, fmt};
use syn::parse::Parser;
use syn::{
    Expr, ExprMatch, ExprPath, FnArg, GenericArgument, Item, ItemEnum, ItemFn, Lit, Pat, PatLit,
    PathArguments, ReturnType, Stmt, Type, TypePath, parse_file,
};

const CORE_HASH_ALGORITHM: &str = "rust-hook-core-json-sha256:v1";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RustHookCoreUnsupportedConstruct {
    pub message: String,
}

impl RustHookCoreUnsupportedConstruct {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for RustHookCoreUnsupportedConstruct {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "unsupported RustHookCore construct: {}",
            self.message
        )
    }
}

impl std::error::Error for RustHookCoreUnsupportedConstruct {}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct RustHookCoreAst {
    pub hash_algorithm: String,
    pub canonical_hash: String,
    pub decision_enums: Vec<RustHookCoreDecisionEnum>,
    pub hooks: Vec<RustHookCoreHook>,
    pub registrations: Vec<RustHookCoreRegistration>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct RustHookCoreDecisionEnum {
    pub name: String,
    pub variants: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RustHookCoreSourceSpan {
    pub line_start: usize,
    pub line_end: usize,
}

impl Default for RustHookCoreSourceSpan {
    fn default() -> Self {
        Self {
            line_start: 1,
            line_end: 1,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct RustHookCoreHook {
    pub name: String,
    pub event: String,
    pub input_type: String,
    pub result_type: String,
    pub decisions: Vec<RustHookCoreDecision>,
    pub event_decisions: Vec<RustHookCoreEventDecision>,
    pub default_decision: Option<RustHookCoreDecision>,
    pub calls: Vec<String>,
    #[serde(skip)]
    pub source_span: RustHookCoreSourceSpan,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct RustHookCoreEventDecision {
    pub event: String,
    pub decision: RustHookCoreDecision,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct RustHookCoreRegistration {
    pub event: String,
    pub callback: String,
    pub kind: RustHookCoreRegistrationKind,
    #[serde(skip)]
    pub source_span: RustHookCoreSourceSpan,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
pub enum RustHookCoreRegistrationKind {
    Inventory,
    Linkme,
    Macro,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
pub enum RustHookCoreDecision {
    Allow,
    Deny,
    Ask,
    Block,
}

pub fn parse_rust_hook_core(
    source: &str,
) -> Result<RustHookCoreAst, RustHookCoreUnsupportedConstruct> {
    let file = parse_file(source).map_err(|error| {
        RustHookCoreUnsupportedConstruct::new(format!("source contains Rust parse errors: {error}"))
    })?;
    reject_dynamic_dispatch(&file)?;
    reject_semantic_attributes(&file)?;
    let event_variants: BTreeSet<String> = file
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Enum(declaration) if declaration.ident == "HookEvent" => Some(declaration),
            _ => None,
        })
        .flat_map(|declaration| {
            declaration
                .variants
                .iter()
                .map(|variant| variant.ident.to_string())
        })
        .collect();
    let mut source_spans = RustHookCoreSpanIndex::new(source);
    let mut ast = RustHookCoreAst {
        hash_algorithm: CORE_HASH_ALGORITHM.to_string(),
        canonical_hash: String::new(),
        decision_enums: Vec::new(),
        hooks: Vec::new(),
        registrations: Vec::new(),
    };
    for item in &file.items {
        match item {
            Item::Use(_) => {}
            Item::Enum(item_enum) => ast.decision_enums.push(parse_decision_enum(item_enum)?),
            Item::Fn(function) => {
                ast.hooks
                    .push(parse_hook_fn(function, &source_spans, &event_variants)?)
            }
            Item::Macro(item_macro) => {
                if item_macro.mac.path.is_ident("register_hook") {
                    let mut registration =
                        registration_from_macro_tokens(&item_macro.mac.tokens.to_string())?;
                    registration.source_span = source_spans
                        .registration_span(&registration)
                        .unwrap_or_default();
                    ast.registrations.push(registration);
                } else {
                    return Err(RustHookCoreUnsupportedConstruct::new(
                        "only register_hook! macros are supported at top level",
                    ));
                }
            }
            _ => {
                return Err(RustHookCoreUnsupportedConstruct::new(
                    "top-level item is outside RustHookCore",
                ));
            }
        }
    }
    ast.decision_enums
        .sort_by(|left, right| left.name.cmp(&right.name));
    ast.hooks.sort_by(|left, right| left.name.cmp(&right.name));
    if ast
        .hooks
        .windows(2)
        .any(|pair| pair[0].name == pair[1].name)
        || ast
            .decision_enums
            .windows(2)
            .any(|pair| pair[0].name == pair[1].name)
    {
        return Err(RustHookCoreUnsupportedConstruct::new(
            "duplicate declaration names are outside RustHookCore",
        ));
    }
    ast.registrations.sort_by(|left, right| {
        left.event
            .cmp(&right.event)
            .then_with(|| left.callback.cmp(&right.callback))
            .then_with(|| left.kind.cmp(&right.kind))
    });
    if ast
        .decision_enums
        .iter()
        .all(|decl| decl.name != "HookResult")
    {
        return Err(RustHookCoreUnsupportedConstruct::new(
            "missing enum HookResult declaration",
        ));
    }
    ast.canonical_hash = canonical_hash(&ast)?;
    Ok(ast)
}

fn parse_decision_enum(
    item_enum: &ItemEnum,
) -> Result<RustHookCoreDecisionEnum, RustHookCoreUnsupportedConstruct> {
    if !item_enum.generics.params.is_empty()
        || item_enum.generics.where_clause.is_some()
        || item_enum.variants.iter().any(|variant| {
            !matches!(variant.fields, syn::Fields::Unit) || variant.discriminant.is_some()
        })
    {
        return Err(RustHookCoreUnsupportedConstruct::new(
            "enum payloads, discriminants and generics are outside RustHookCore",
        ));
    }
    let name = item_enum.ident.to_string();
    let variants = item_enum
        .variants
        .iter()
        .map(|variant| variant.ident.to_string())
        .collect::<Vec<_>>();
    if name != "HookResult"
        && variants
            .iter()
            .any(|variant| decision_from_variant(variant).is_some())
    {
        return Err(RustHookCoreUnsupportedConstruct::new(
            "decision variants must be declared on enum HookResult",
        ));
    }
    if name == "HookResult" {
        for variant in &variants {
            if decision_from_variant(variant).is_none() {
                return Err(RustHookCoreUnsupportedConstruct::new(format!(
                    "HookResult variant '{variant}' is outside RustHookCore"
                )));
            }
        }
    }
    Ok(RustHookCoreDecisionEnum { name, variants })
}

fn parse_hook_fn(
    function: &ItemFn,
    source_spans: &RustHookCoreSpanIndex<'_>,
    event_variants: &BTreeSet<String>,
) -> Result<RustHookCoreHook, RustHookCoreUnsupportedConstruct> {
    let name = function.sig.ident.to_string();
    if function.sig.asyncness.is_some()
        || function.sig.unsafety.is_some()
        || function.sig.constness.is_some()
        || function.sig.abi.is_some()
        || function.sig.variadic.is_some()
        || function.sig.generics.where_clause.is_some()
        || !function.sig.generics.params.is_empty()
    {
        return Err(RustHookCoreUnsupportedConstruct::new(
            "hook function qualifiers or generics are outside RustHookCore",
        ));
    }
    let (input_name, input_type) = single_input(function)?;
    let result_type = return_type(&function.sig.output)?;
    if !name.starts_with("on_") || input_type != "HookInput" || result_type != "HookResult" {
        return Err(RustHookCoreUnsupportedConstruct::new(
            "hook functions must have signature fn on_<event>(input: HookInput) -> HookResult",
        ));
    }
    let mut body = Body::default();
    collect_stmts(
        &function.block.stmts,
        &input_name,
        event_variants,
        &mut body,
    )?;
    let source_span = source_spans.function_span(&name).unwrap_or_default();
    Ok(RustHookCoreHook {
        event: name.trim_start_matches("on_").to_string(),
        name,
        input_type,
        result_type,
        decisions: stable_decisions(body.decisions),
        event_decisions: body.event_decisions,
        default_decision: body.default_decision,
        calls: body.calls,
        source_span,
    })
}

#[derive(Default)]
struct Body {
    decisions: Vec<RustHookCoreDecision>,
    event_decisions: Vec<RustHookCoreEventDecision>,
    default_decision: Option<RustHookCoreDecision>,
    calls: Vec<String>,
}

// Only a returned value or the final expression determines the summary. In
// particular, a discarded match is not a return. Named, argument-free call
// statements are retained as opaque labels; their effects are not verified.
fn collect_stmts(
    stmts: &[Stmt],
    input_name: &str,
    event_variants: &BTreeSet<String>,
    body: &mut Body,
) -> Result<(), RustHookCoreUnsupportedConstruct> {
    let mut result_start = 0;
    for statement in stmts {
        let Stmt::Expr(Expr::Call(call), Some(_)) = statement else {
            break;
        };
        let name = match call.func.as_ref() {
            Expr::Path(path) if path.qself.is_none() && call.args.is_empty() => {
                path.path.get_ident()
            }
            _ => None,
        }
        .ok_or_else(|| {
            RustHookCoreUnsupportedConstruct::new(
                "opaque call statements require an unqualified identifier and no arguments",
            )
        })?;
        body.calls.push(name.to_string());
        result_start += 1;
    }
    let stmts = &stmts[result_start..];
    match stmts.first() {
        Some(Stmt::Expr(Expr::Return(expr_return), _)) => {
            let Some(returned) = &expr_return.expr else {
                return Err(RustHookCoreUnsupportedConstruct::new(
                    "empty return is outside RustHookCore",
                ));
            };
            // Remaining statements are unreachable after an explicit return.
            collect_result(returned, input_name, event_variants, body)
        }
        Some(Stmt::Expr(expr, None)) if stmts.len() == 1 => {
            collect_result(expr, input_name, event_variants, body)
        }
        _ => Err(RustHookCoreUnsupportedConstruct::new(
            "hook body must directly return a result or end in a single result expression; discarded expressions and locals are outside RustHookCore",
        )),
    }
}

fn collect_result(
    expr: &Expr,
    input_name: &str,
    event_variants: &BTreeSet<String>,
    body: &mut Body,
) -> Result<(), RustHookCoreUnsupportedConstruct> {
    match expr {
        Expr::Path(_) => push_decision(expr, body),
        Expr::Match(expr_match) => collect_match(expr_match, input_name, event_variants, body),
        _ => Err(RustHookCoreUnsupportedConstruct::new(
            "hook result must be a HookResult variant or an event match; calls are outside RustHookCore",
        )),
    }
}

fn push_decision(expr: &Expr, body: &mut Body) -> Result<(), RustHookCoreUnsupportedConstruct> {
    let decision = decision_from_expr(expr)?;
    body.decisions.push(decision.clone());
    body.default_decision.get_or_insert(decision);
    Ok(())
}

fn collect_match(
    expr_match: &ExprMatch,
    input_name: &str,
    event_variants: &BTreeSet<String>,
    body: &mut Body,
) -> Result<(), RustHookCoreUnsupportedConstruct> {
    let is_input_event = match expr_match.expr.as_ref() {
        Expr::Field(field) if matches!(&field.member, syn::Member::Named(name) if name == "event") =>
        {
            matches!(field.base.as_ref(), Expr::Path(path)
                if path.qself.is_none() && path.path.is_ident(input_name))
        }
        _ => false,
    };
    if !is_input_event {
        return Err(RustHookCoreUnsupportedConstruct::new(
            "match scrutinee must be the hook parameter's event field",
        ));
    }
    let mut events = BTreeSet::new();
    for (index, arm) in expr_match.arms.iter().enumerate() {
        if arm.guard.is_some() {
            return Err(RustHookCoreUnsupportedConstruct::new(
                "match guards are outside RustHookCore",
            ));
        }
        let decision = decision_from_expr(&arm.body)?;
        if matches!(arm.pat, Pat::Wild(_)) {
            if index + 1 != expr_match.arms.len() {
                return Err(RustHookCoreUnsupportedConstruct::new(
                    "match wildcard must be the final arm",
                ));
            }
            body.default_decision = Some(decision.clone());
        } else {
            let event = event_from_pat(&arm.pat, event_variants)?;
            if !events.insert(event.clone()) {
                return Err(RustHookCoreUnsupportedConstruct::new(
                    "duplicate event patterns are outside RustHookCore",
                ));
            }
            body.event_decisions.push(RustHookCoreEventDecision {
                event,
                decision: decision.clone(),
            });
        }
        body.decisions.push(decision);
    }
    if body.default_decision.is_none() {
        return Err(RustHookCoreUnsupportedConstruct::new(
            "event match requires a final wildcard default",
        ));
    }
    // Distinct literal arms do not overlap; sorting cannot change precedence.
    body.event_decisions
        .sort_by(|left, right| left.event.cmp(&right.event));
    Ok(())
}

fn decision_from_expr(
    expr: &Expr,
) -> Result<RustHookCoreDecision, RustHookCoreUnsupportedConstruct> {
    let Expr::Path(ExprPath {
        path, qself: None, ..
    }) = expr
    else {
        return Err(RustHookCoreUnsupportedConstruct::new(
            "returns and match arms must directly produce HookResult variants",
        ));
    };
    if path.leading_colon.is_some()
        || path
            .segments
            .iter()
            .any(|segment| !matches!(segment.arguments, PathArguments::None))
    {
        return Err(RustHookCoreUnsupportedConstruct::new(
            "qualified or generic result paths are outside RustHookCore",
        ));
    }
    let segments = path
        .segments
        .iter()
        .map(|segment| segment.ident.to_string())
        .collect::<Vec<_>>();
    match segments.as_slice() {
        [enum_name, variant] if enum_name == "HookResult" => decision_from_variant(variant)
            .ok_or_else(|| {
                RustHookCoreUnsupportedConstruct::new(format!(
                    "unknown HookResult variant '{variant}'"
                ))
            }),
        [enum_name, variant] if decision_from_variant(variant).is_some() => {
            Err(RustHookCoreUnsupportedConstruct::new(format!(
                "decision variant {variant} is returned from renamed enum {enum_name}"
            )))
        }
        _ => Err(RustHookCoreUnsupportedConstruct::new(
            "return expression is not a HookResult variant",
        )),
    }
}

pub fn decision_from_literal(literal: &str) -> Option<RustHookCoreDecision> {
    match literal {
        "allow" | "Allow" => Some(RustHookCoreDecision::Allow),
        "deny" | "Deny" => Some(RustHookCoreDecision::Deny),
        "ask" | "Ask" => Some(RustHookCoreDecision::Ask),
        "block" | "Block" => Some(RustHookCoreDecision::Block),
        _ => None,
    }
}

fn decision_from_variant(variant: &str) -> Option<RustHookCoreDecision> {
    decision_from_literal(variant)
}

fn event_from_pat(
    pat: &Pat,
    event_variants: &BTreeSet<String>,
) -> Result<String, RustHookCoreUnsupportedConstruct> {
    match pat {
        Pat::Lit(PatLit {
            lit: Lit::Str(lit), ..
        }) => Ok(lit.value()),
        Pat::Path(path)
            if path.qself.is_none()
                && path.path.leading_colon.is_none()
                && path.path.segments.len() == 2
                && path
                    .path
                    .segments
                    .iter()
                    .all(|segment| matches!(segment.arguments, PathArguments::None))
                && path.path.segments[0].ident == "HookEvent"
                && event_variants.contains(&path.path.segments[1].ident.to_string()) =>
        {
            Ok(path.path.segments[1].ident.to_string())
        }
        _ => Err(RustHookCoreUnsupportedConstruct::new(
            "match arms require string literals, locally declared HookEvent variants or a wildcard default",
        )),
    }
}

fn single_input(function: &ItemFn) -> Result<(String, String), RustHookCoreUnsupportedConstruct> {
    let mut inputs = function.sig.inputs.iter();
    let Some(FnArg::Typed(input)) = inputs.next() else {
        return Err(RustHookCoreUnsupportedConstruct::new(
            "hook function must take one typed HookInput parameter",
        ));
    };
    if inputs.next().is_some() {
        return Err(RustHookCoreUnsupportedConstruct::new(
            "hook function must take exactly one HookInput parameter",
        ));
    }
    let Pat::Ident(binding) = input.pat.as_ref() else {
        return Err(RustHookCoreUnsupportedConstruct::new(
            "hook parameter must be a simple identifier",
        ));
    };
    if binding.by_ref.is_some() || binding.subpat.is_some() {
        return Err(RustHookCoreUnsupportedConstruct::new(
            "hook parameter must be a simple identifier",
        ));
    }
    Ok((binding.ident.to_string(), type_name(&input.ty)?))
}

fn return_type(output: &ReturnType) -> Result<String, RustHookCoreUnsupportedConstruct> {
    match output {
        ReturnType::Type(_, ty) => type_name(ty),
        ReturnType::Default => Err(RustHookCoreUnsupportedConstruct::new(
            "hook function must return HookResult",
        )),
    }
}

fn type_name(ty: &Type) -> Result<String, RustHookCoreUnsupportedConstruct> {
    match ty {
        Type::Path(TypePath { path, qself: None }) if path.get_ident().is_some() => path
            .segments
            .last()
            .map(|segment| segment.ident.to_string())
            .ok_or_else(|| RustHookCoreUnsupportedConstruct::new("empty type path")),
        Type::TraitObject(_) | Type::ImplTrait(_) => Err(RustHookCoreUnsupportedConstruct::new(
            "dynamic dispatch is outside RustHookCore",
        )),
        _ => Err(RustHookCoreUnsupportedConstruct::new(
            "hook signature type is outside RustHookCore",
        )),
    }
}

fn reject_semantic_attributes(file: &syn::File) -> Result<(), RustHookCoreUnsupportedConstruct> {
    struct Attributes {
        unsupported: bool,
    }
    impl<'ast> syn::visit::Visit<'ast> for Attributes {
        fn visit_attribute(&mut self, attribute: &'ast syn::Attribute) {
            if !["doc", "allow", "warn", "deny", "forbid"]
                .iter()
                .any(|name| attribute.path().is_ident(name))
            {
                self.unsupported = true;
            }
        }
    }
    let mut attributes = Attributes { unsupported: false };
    syn::visit::Visit::visit_file(&mut attributes, file);
    if attributes.unsupported {
        return Err(RustHookCoreUnsupportedConstruct::new(
            "conditional compilation and transforming attributes are outside RustHookCore",
        ));
    }
    Ok(())
}

fn reject_dynamic_dispatch(file: &syn::File) -> Result<(), RustHookCoreUnsupportedConstruct> {
    for item in &file.items {
        reject_dynamic_dispatch_item(item)?;
    }
    Ok(())
}

fn reject_dynamic_dispatch_item(item: &Item) -> Result<(), RustHookCoreUnsupportedConstruct> {
    match item {
        Item::Fn(function) => {
            for input in &function.sig.inputs {
                if let FnArg::Typed(input) = input
                    && type_contains_dynamic_dispatch(&input.ty)
                {
                    return dynamic_dispatch_error();
                }
            }
            if let ReturnType::Type(_, ty) = &function.sig.output
                && type_contains_dynamic_dispatch(ty)
            {
                return dynamic_dispatch_error();
            }
            reject_dynamic_dispatch_stmts(&function.block.stmts)
        }
        Item::Type(item_type) if type_contains_dynamic_dispatch(&item_type.ty) => {
            dynamic_dispatch_error()
        }
        _ => Ok(()),
    }
}

fn reject_dynamic_dispatch_stmts(stmts: &[Stmt]) -> Result<(), RustHookCoreUnsupportedConstruct> {
    for stmt in stmts {
        if let Stmt::Local(local) = stmt
            && pat_contains_dynamic_dispatch(&local.pat)
        {
            return dynamic_dispatch_error();
        }
    }
    Ok(())
}

fn pat_contains_dynamic_dispatch(pat: &Pat) -> bool {
    match pat {
        Pat::Type(pat_type) => type_contains_dynamic_dispatch(&pat_type.ty),
        Pat::Reference(reference) => pat_contains_dynamic_dispatch(&reference.pat),
        Pat::Tuple(tuple) => tuple.elems.iter().any(pat_contains_dynamic_dispatch),
        Pat::TupleStruct(tuple) => tuple.elems.iter().any(pat_contains_dynamic_dispatch),
        Pat::Slice(slice) => slice.elems.iter().any(pat_contains_dynamic_dispatch),
        Pat::Struct(pat_struct) => pat_struct
            .fields
            .iter()
            .any(|field| pat_contains_dynamic_dispatch(&field.pat)),
        Pat::Or(pat_or) => pat_or.cases.iter().any(pat_contains_dynamic_dispatch),
        _ => false,
    }
}

fn type_contains_dynamic_dispatch(ty: &Type) -> bool {
    match ty {
        Type::TraitObject(_) | Type::ImplTrait(_) => true,
        Type::Array(array) => type_contains_dynamic_dispatch(&array.elem),
        Type::BareFn(function) => {
            function
                .inputs
                .iter()
                .any(|input| type_contains_dynamic_dispatch(&input.ty))
                || matches!(
                    &function.output,
                    ReturnType::Type(_, ty) if type_contains_dynamic_dispatch(ty)
                )
        }
        Type::Group(group) => type_contains_dynamic_dispatch(&group.elem),
        Type::Paren(paren) => type_contains_dynamic_dispatch(&paren.elem),
        Type::Path(type_path) => type_path
            .path
            .segments
            .iter()
            .any(|segment| path_arguments_contain_dynamic_dispatch(&segment.arguments)),
        Type::Ptr(pointer) => type_contains_dynamic_dispatch(&pointer.elem),
        Type::Reference(reference) => type_contains_dynamic_dispatch(&reference.elem),
        Type::Slice(slice) => type_contains_dynamic_dispatch(&slice.elem),
        Type::Tuple(tuple) => tuple.elems.iter().any(type_contains_dynamic_dispatch),
        _ => false,
    }
}

fn path_arguments_contain_dynamic_dispatch(arguments: &PathArguments) -> bool {
    match arguments {
        PathArguments::None => false,
        PathArguments::Parenthesized(arguments) => {
            arguments.inputs.iter().any(type_contains_dynamic_dispatch)
                || matches!(
                    &arguments.output,
                    ReturnType::Type(_, ty) if type_contains_dynamic_dispatch(ty)
                )
        }
        PathArguments::AngleBracketed(arguments) => {
            arguments.args.iter().any(|argument| match argument {
                GenericArgument::Type(ty) => type_contains_dynamic_dispatch(ty),
                GenericArgument::AssocType(assoc) => type_contains_dynamic_dispatch(&assoc.ty),
                _ => false,
            })
        }
    }
}

fn dynamic_dispatch_error<T>() -> Result<T, RustHookCoreUnsupportedConstruct> {
    Err(RustHookCoreUnsupportedConstruct::new(
        "dynamic dispatch is outside RustHookCore",
    ))
}

fn registration_from_macro_tokens(
    tokens: &str,
) -> Result<RustHookCoreRegistration, RustHookCoreUnsupportedConstruct> {
    let arguments = syn::punctuated::Punctuated::<Expr, syn::Token![,]>::parse_terminated
        .parse_str(tokens)
        .map_err(|_| {
            RustHookCoreUnsupportedConstruct::new(
                "register_hook! requires exactly a string event and a callback identifier",
            )
        })?;
    if arguments.len() != 2 {
        return Err(RustHookCoreUnsupportedConstruct::new(
            "register_hook! requires exactly a string event and a callback identifier",
        ));
    }
    let event = match &arguments[0] {
        Expr::Lit(literal) if literal.attrs.is_empty() => match &literal.lit {
            Lit::Str(event) => event.value(),
            _ => {
                return Err(RustHookCoreUnsupportedConstruct::new(
                    "register_hook! event must be a string literal",
                ));
            }
        },
        _ => {
            return Err(RustHookCoreUnsupportedConstruct::new(
                "register_hook! event must be a string literal",
            ));
        }
    };
    let callback = match &arguments[1] {
        Expr::Path(path) if path.qself.is_none() && path.attrs.is_empty() => {
            path.path.get_ident().map(ToString::to_string)
        }
        _ => None,
    }
    .ok_or_else(|| {
        RustHookCoreUnsupportedConstruct::new(
            "register_hook! callback must be an unqualified identifier",
        )
    })?;
    Ok(RustHookCoreRegistration {
        event,
        callback,
        kind: RustHookCoreRegistrationKind::Macro,
        source_span: RustHookCoreSourceSpan::default(),
    })
}

fn stable_decisions(mut decisions: Vec<RustHookCoreDecision>) -> Vec<RustHookCoreDecision> {
    decisions.sort();
    decisions.dedup();
    decisions
}

fn canonical_hash(ast: &RustHookCoreAst) -> Result<String, RustHookCoreUnsupportedConstruct> {
    let mut canonical = ast.clone();
    canonical.canonical_hash.clear();
    let bytes = serde_json::to_vec(&canonical).map_err(|error| {
        RustHookCoreUnsupportedConstruct::new(format!(
            "failed to serialize canonical RustHookCore AST: {error}"
        ))
    })?;
    Ok(format!("{:x}", Sha256::digest(bytes)))
}
