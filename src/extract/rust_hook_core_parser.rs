use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::fmt;
use syn::{
    Expr, ExprCall, ExprMatch, ExprPath, FnArg, GenericArgument, Item, ItemEnum, ItemFn, Lit, Pat,
    PatLit, PathArguments, ReturnType, Stmt, Type, TypePath, parse_file,
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
            Item::Fn(function) => ast.hooks.push(parse_hook_fn(function, &source_spans)?),
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
) -> Result<RustHookCoreHook, RustHookCoreUnsupportedConstruct> {
    let name = function.sig.ident.to_string();
    if function.sig.asyncness.is_some()
        || function.sig.unsafety.is_some()
        || !function.sig.generics.params.is_empty()
    {
        return Err(RustHookCoreUnsupportedConstruct::new(
            "hook function qualifiers or generics are outside RustHookCore",
        ));
    }
    let input_type = single_input_type(function)?;
    let result_type = return_type(&function.sig.output)?;
    if !name.starts_with("on_") || input_type != "HookInput" || result_type != "HookResult" {
        return Err(RustHookCoreUnsupportedConstruct::new(
            "hook functions must have signature fn on_<event>(input: HookInput) -> HookResult",
        ));
    }
    let mut body = Body::default();
    collect_stmts(&function.block.stmts, &mut body)?;
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

fn collect_stmts(stmts: &[Stmt], body: &mut Body) -> Result<(), RustHookCoreUnsupportedConstruct> {
    for stmt in stmts {
        match stmt {
            Stmt::Expr(expr, _) => {
                collect_expr(expr, body)?;
                if matches!(expr, Expr::Return(_) | Expr::Path(_) | Expr::Match(_)) {
                    break;
                }
            }
            Stmt::Local(local) if local.init.is_none() => {}
            _ => {
                return Err(RustHookCoreUnsupportedConstruct::new(
                    "hook body statement is outside RustHookCore",
                ));
            }
        }
    }
    Ok(())
}

fn collect_expr(expr: &Expr, body: &mut Body) -> Result<(), RustHookCoreUnsupportedConstruct> {
    match expr {
        Expr::Return(expr_return) => {
            let Some(returned) = &expr_return.expr else {
                return Err(RustHookCoreUnsupportedConstruct::new(
                    "empty return is outside RustHookCore",
                ));
            };
            push_decision(returned, body)
        }
        Expr::Path(_) => push_decision(expr, body),
        Expr::Match(expr_match) => collect_match(expr_match, body),
        Expr::Call(ExprCall { func, .. }) => {
            let Expr::Path(path) = func.as_ref() else {
                return Err(RustHookCoreUnsupportedConstruct::new(
                    "indirect calls are outside RustHookCore",
                ));
            };
            body.calls.push(
                last_path_ident(path)
                    .ok_or_else(|| RustHookCoreUnsupportedConstruct::new("empty callback path"))?,
            );
            Ok(())
        }
        _ => Err(RustHookCoreUnsupportedConstruct::new(
            "hook expression is outside RustHookCore",
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
    body: &mut Body,
) -> Result<(), RustHookCoreUnsupportedConstruct> {
    for arm in &expr_match.arms {
        let decision = decision_from_expr(&arm.body)?;
        if matches!(arm.pat, Pat::Wild(_)) {
            body.default_decision = Some(decision.clone());
        } else {
            body.event_decisions.push(RustHookCoreEventDecision {
                event: event_from_pat(&arm.pat)?,
                decision: decision.clone(),
            });
        }
        body.decisions.push(decision);
    }
    body.event_decisions
        .sort_by(|left, right| left.event.cmp(&right.event));
    Ok(())
}

fn decision_from_expr(
    expr: &Expr,
) -> Result<RustHookCoreDecision, RustHookCoreUnsupportedConstruct> {
    let Expr::Path(ExprPath { path, .. }) = expr else {
        return Err(RustHookCoreUnsupportedConstruct::new(
            "returns and match arms must directly produce HookResult variants",
        ));
    };
    let segments = path
        .segments
        .iter()
        .map(|segment| segment.ident.to_string())
        .collect::<Vec<_>>();
    match segments.as_slice() {
        [variant] => decision_from_variant(variant).ok_or_else(|| {
            RustHookCoreUnsupportedConstruct::new(format!("unknown HookResult variant '{variant}'"))
        }),
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

fn event_from_pat(pat: &Pat) -> Result<String, RustHookCoreUnsupportedConstruct> {
    match pat {
        Pat::Lit(PatLit {
            lit: Lit::Str(lit), ..
        }) => Ok(lit.value()),
        Pat::Path(path) => path
            .path
            .segments
            .last()
            .map(|segment| segment.ident.to_string())
            .ok_or_else(|| RustHookCoreUnsupportedConstruct::new("empty event path")),
        _ => Err(RustHookCoreUnsupportedConstruct::new(
            "match arms must use event paths, string literals, or wildcard defaults",
        )),
    }
}

fn single_input_type(function: &ItemFn) -> Result<String, RustHookCoreUnsupportedConstruct> {
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
    type_name(&input.ty)
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
        Type::Path(TypePath { path, .. }) => path
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
    let event = first_string_literal(tokens).ok_or_else(|| {
        RustHookCoreUnsupportedConstruct::new("register_hook! requires a string event")
    })?;
    let callback = tokens
        .split(|character: char| !character.is_alphanumeric() && character != '_')
        .rfind(|part| {
            !part.is_empty()
                && part
                    .chars()
                    .next()
                    .is_some_and(|ch| ch.is_alphabetic() || ch == '_')
        })
        .ok_or_else(|| {
            RustHookCoreUnsupportedConstruct::new("register_hook! requires a callback identifier")
        })?
        .to_string();
    Ok(RustHookCoreRegistration {
        event,
        callback,
        kind: RustHookCoreRegistrationKind::Macro,
        source_span: RustHookCoreSourceSpan::default(),
    })
}

fn first_string_literal(text: &str) -> Option<String> {
    let start = text.find('"')? + 1;
    let end = text[start..].find('"')? + start;
    Some(text[start..end].to_string())
}

fn last_path_ident(path: &ExprPath) -> Option<String> {
    path.path
        .segments
        .last()
        .map(|segment| segment.ident.to_string())
}

fn stable_decisions(mut decisions: Vec<RustHookCoreDecision>) -> Vec<RustHookCoreDecision> {
    decisions.sort();
    decisions.dedup();
    decisions
}

#[derive(Clone, Copy)]
struct ByteSpan {
    start: usize,
    end: usize,
}

struct RustHookCoreSpanIndex<'source> {
    source: &'source str,
    mask: Vec<u8>,
    registration_spans: Vec<ByteSpan>,
}

impl<'source> RustHookCoreSpanIndex<'source> {
    fn new(source: &'source str) -> Self {
        let mask = rust_source_mask(source);
        let registration_spans = collect_registration_spans(&mask);
        Self {
            source,
            mask,
            registration_spans,
        }
    }

    fn function_span(&self, name: &str) -> Option<RustHookCoreSourceSpan> {
        let bytes = self.mask.as_slice();
        let mut cursor = 0;
        while let Some(fn_index) = find_token(bytes, cursor, b"fn") {
            let name_start = skip_ascii_whitespace(bytes, fn_index + 2);
            let name_end = name_start.checked_add(name.len())?;
            if bytes.get(name_start..name_end) == Some(name.as_bytes())
                && is_token_boundary(bytes, name_end)
            {
                let open_brace = find_byte(bytes, name_end, b'{')?;
                let close_brace = matching_delimiter(bytes, open_brace, b'{', b'}')?;
                return Some(self.source_span(fn_index, close_brace));
            }
            cursor = fn_index + 2;
        }
        None
    }

    fn registration_span(
        &mut self,
        registration: &RustHookCoreRegistration,
    ) -> Option<RustHookCoreSourceSpan> {
        let index = self.registration_spans.iter().position(|span| {
            let snippet = &self.source[span.start..=span.end];
            registration_from_macro_tokens(snippet).is_ok_and(|candidate| {
                candidate.event == registration.event && candidate.callback == registration.callback
            })
        })?;
        let span = self.registration_spans.remove(index);
        Some(self.source_span(span.start, span.end))
    }

    fn source_span(&self, start: usize, end: usize) -> RustHookCoreSourceSpan {
        RustHookCoreSourceSpan {
            line_start: line_number_at(self.source, start),
            line_end: line_number_at(self.source, end),
        }
    }
}

fn collect_registration_spans(mask: &[u8]) -> Vec<ByteSpan> {
    let mut spans = Vec::new();
    let mut cursor = 0;
    while let Some(start) = find_token(mask, cursor, b"register_hook") {
        let bang = skip_ascii_whitespace(mask, start + "register_hook".len());
        if mask.get(bang) != Some(&b'!') {
            cursor = start + "register_hook".len();
            continue;
        }
        let delimiter_start = skip_ascii_whitespace(mask, bang + 1);
        let Some((open, close)) = mask.get(delimiter_start).and_then(delimiter_pair) else {
            cursor = bang + 1;
            continue;
        };
        let Some(delimiter_end) = matching_delimiter(mask, delimiter_start, open, close) else {
            cursor = delimiter_start + 1;
            continue;
        };
        let semicolon = skip_ascii_whitespace(mask, delimiter_end + 1);
        let end = if mask.get(semicolon) == Some(&b';') {
            semicolon
        } else {
            delimiter_end
        };
        spans.push(ByteSpan { start, end });
        cursor = end + 1;
    }
    spans
}

fn rust_source_mask(source: &str) -> Vec<u8> {
    let bytes = source.as_bytes();
    let mut mask = bytes.to_vec();
    let mut index = 0;
    while index < bytes.len() {
        if let Some(end) = raw_string_end(bytes, index) {
            mask_range(&mut mask, index, end);
            index = end + 1;
        } else if bytes.get(index..index + 2) == Some(b"//") {
            let end = find_line_end(bytes, index + 2);
            mask_range(&mut mask, index, end.saturating_sub(1));
            index = end;
        } else if bytes.get(index..index + 2) == Some(b"/*") {
            let end = block_comment_end(bytes, index + 2);
            mask_range(&mut mask, index, end);
            index = end + 1;
        } else if bytes[index] == b'"' {
            let end = quoted_literal_end(bytes, index, b'"');
            mask_range(&mut mask, index, end);
            index = end + 1;
        } else if bytes[index] == b'\'' && !is_lifetime_start(bytes, index) {
            let end = quoted_literal_end(bytes, index, b'\'');
            mask_range(&mut mask, index, end);
            index = end + 1;
        } else {
            index += 1;
        }
    }
    mask
}

fn mask_range(mask: &mut [u8], start: usize, end: usize) {
    let bounded_end = end.min(mask.len().saturating_sub(1));
    for byte in &mut mask[start..=bounded_end] {
        if *byte != b'\n' && *byte != b'\r' {
            *byte = b' ';
        }
    }
}

fn raw_string_end(bytes: &[u8], start: usize) -> Option<usize> {
    let mut index = start;
    if bytes.get(index) == Some(&b'b') && bytes.get(index + 1) == Some(&b'r') {
        index += 1;
    }
    if bytes.get(index) != Some(&b'r') {
        return None;
    }
    let mut hashes = 0;
    let mut quote_index = index + 1;
    while bytes.get(quote_index) == Some(&b'#') {
        hashes += 1;
        quote_index += 1;
    }
    if bytes.get(quote_index) != Some(&b'"') {
        return None;
    }
    let mut cursor = quote_index + 1;
    while cursor < bytes.len() {
        if bytes[cursor] == b'"'
            && bytes
                .get(cursor + 1..cursor + 1 + hashes)
                .is_some_and(|suffix| suffix.iter().all(|byte| *byte == b'#'))
        {
            return Some(cursor + hashes);
        }
        cursor += 1;
    }
    Some(bytes.len().saturating_sub(1))
}

fn quoted_literal_end(bytes: &[u8], start: usize, quote: u8) -> usize {
    let mut cursor = start + 1;
    while cursor < bytes.len() {
        if bytes[cursor] == b'\\' {
            cursor += 2;
        } else if bytes[cursor] == quote {
            return cursor;
        } else {
            cursor += 1;
        }
    }
    bytes.len().saturating_sub(1)
}

fn block_comment_end(bytes: &[u8], start: usize) -> usize {
    let mut depth = 1;
    let mut cursor = start;
    while cursor + 1 < bytes.len() {
        if bytes.get(cursor..cursor + 2) == Some(b"/*") {
            depth += 1;
            cursor += 2;
        } else if bytes.get(cursor..cursor + 2) == Some(b"*/") {
            depth -= 1;
            cursor += 2;
            if depth == 0 {
                return cursor - 1;
            }
        } else {
            cursor += 1;
        }
    }
    bytes.len().saturating_sub(1)
}

fn find_line_end(bytes: &[u8], start: usize) -> usize {
    bytes[start..]
        .iter()
        .position(|byte| *byte == b'\n')
        .map(|offset| start + offset)
        .unwrap_or(bytes.len())
}

fn is_lifetime_start(bytes: &[u8], index: usize) -> bool {
    bytes
        .get(index + 1)
        .is_some_and(|byte| byte.is_ascii_alphabetic() || *byte == b'_')
}

fn find_token(bytes: &[u8], mut cursor: usize, token: &[u8]) -> Option<usize> {
    while cursor + token.len() <= bytes.len() {
        let index = find_bytes(bytes, cursor, token)?;
        let end = index + token.len();
        if is_token_boundary_before(bytes, index) && is_token_boundary(bytes, end) {
            return Some(index);
        }
        cursor = end;
    }
    None
}

fn find_bytes(bytes: &[u8], start: usize, needle: &[u8]) -> Option<usize> {
    bytes[start..]
        .windows(needle.len())
        .position(|window| window == needle)
        .map(|offset| start + offset)
}

fn find_byte(bytes: &[u8], start: usize, needle: u8) -> Option<usize> {
    bytes[start..]
        .iter()
        .position(|byte| *byte == needle)
        .map(|offset| start + offset)
}

fn skip_ascii_whitespace(bytes: &[u8], mut cursor: usize) -> usize {
    while bytes
        .get(cursor)
        .is_some_and(|byte| byte.is_ascii_whitespace())
    {
        cursor += 1;
    }
    cursor
}

fn is_token_boundary_before(bytes: &[u8], index: usize) -> bool {
    index == 0 || is_token_boundary(bytes, index - 1)
}

fn is_token_boundary(bytes: &[u8], index: usize) -> bool {
    !bytes
        .get(index)
        .is_some_and(|byte| byte.is_ascii_alphanumeric() || *byte == b'_')
}

fn delimiter_pair(open: &u8) -> Option<(u8, u8)> {
    match open {
        b'(' => Some((*open, b')')),
        b'[' => Some((*open, b']')),
        b'{' => Some((*open, b'}')),
        _ => None,
    }
}

fn matching_delimiter(bytes: &[u8], open_index: usize, open: u8, close: u8) -> Option<usize> {
    let mut depth = 0;
    for (offset, byte) in bytes[open_index..].iter().enumerate() {
        if *byte == open {
            depth += 1;
        } else if *byte == close {
            depth -= 1;
            if depth == 0 {
                return Some(open_index + offset);
            }
        }
    }
    None
}

fn line_number_at(source: &str, byte_index: usize) -> usize {
    source.as_bytes()[..byte_index.min(source.len())]
        .iter()
        .filter(|byte| **byte == b'\n')
        .count()
        + 1
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
