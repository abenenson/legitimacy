pub(super) fn verify_sanitizer_reconciliation_tests(source: &str) -> Result<(), &'static str> {
    verify_exact_tests(
        source,
        &[
            "sanitizer_contract_registry_matches_independent_ordered_registry",
            "sanitizer_contract_registry_rejects_all_ordered_list_shape_drift",
            "normative_sanitizer_omission_reaches_specific_edge",
        ],
        "reconciliation-test-shape",
    )
}

pub(super) fn verify_sanitizer_structural_controls(source: &str) -> Result<(), &'static str> {
    verify_exact_tests(
        source,
        &[
            "sanitizer_reconciliation_functions_remain_tests",
            "independent_sanitizer_registry_accessor_returns_single_authority",
            "normative_verifier_propagates_sanitizer_registry_reconciliation",
        ],
        "sanitizer-control-test-shape",
    )
}

pub(super) fn verify_sanitizer_registry_authority(source: &str) -> Result<(), &'static str> {
    const ERROR: &str = "sanitizer-registry-authority";
    const PATHS: [&str; 4] = [
        "src/trajectory/codex_exec_v0/sanitizer.rs",
        "src/trajectory/codex_exec_v0/sanitizer_jwt.rs",
        "src/trajectory/codex_exec_v0/publication_authority.rs",
        "src/trajectory/codex_exec_v0/lineage_sidecar.rs",
    ];

    let syntax = syn::parse_file(source).map_err(|_| ERROR)?;
    let paths = syntax
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Const(item) if item.ident == "SANITIZER_ONLY_PATHS" => Some(item),
            _ => None,
        })
        .collect::<Vec<_>>();
    if paths.len() != 1
        || !paths[0].attrs.is_empty()
        || !restricted_visibility_is(&paths[0].vis, "super")
        || !str_slice_reference_type(paths[0].ty.as_ref(), None, None)
        || referenced_string_array(paths[0].expr.as_ref())
            != Some(PATHS.into_iter().map(str::to_string).collect())
    {
        return Err(ERROR);
    }

    let accessors = syntax
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Fn(item) if item.sig.ident == "independent_sanitizer_only_paths" => {
                Some(item)
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    let [accessor] = accessors.as_slice() else {
        return Err(ERROR);
    };
    if !accessor.attrs.is_empty()
        || !restricted_visibility_is(&accessor.vis, "super")
        || !plain_free_function_signature(&accessor.sig)
        || !matches!(
            &accessor.sig.output,
            syn::ReturnType::Type(_, ty)
                if str_slice_reference_type(ty, Some("static"), Some("static"))
        )
        || !matches!(
            accessor.block.stmts.as_slice(),
            [syn::Stmt::Expr(syn::Expr::Path(path), None)]
                if path_is_bare_ident(path, "SANITIZER_ONLY_PATHS")
        )
        || syntax.items.iter().any(|item| {
            matches!(item, syn::Item::Mod(module) if module.ident == "sanitizer_registry")
                || matches!(item, syn::Item::Struct(item) if item.ident == "SanitizerRegistry")
                || matches!(item, syn::Item::Static(item) if type_is_named(item.ty.as_ref(), "SanitizerRegistry"))
        })
    {
        return Err(ERROR);
    }
    Ok(())
}

fn referenced_string_array(expression: &syn::Expr) -> Option<Vec<String>> {
    let syn::Expr::Reference(reference) = expression else {
        return None;
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        return None;
    };
    array
        .elems
        .iter()
        .map(|element| match element {
            syn::Expr::Lit(syn::ExprLit {
                lit: syn::Lit::Str(value),
                ..
            }) => Some(value.value()),
            _ => None,
        })
        .collect()
}

fn restricted_visibility_is(visibility: &syn::Visibility, expected: &str) -> bool {
    matches!(visibility, syn::Visibility::Restricted(restricted)
        if restricted.in_token.is_none() && restricted.path.is_ident(expected))
}

fn type_is_named(item: &syn::Type, expected: &str) -> bool {
    matches!(item, syn::Type::Path(path)
        if path.qself.is_none() && path.path.leading_colon.is_none() && path.path.is_ident(expected))
}

fn lifetime_is(reference: &syn::TypeReference, expected: Option<&str>) -> bool {
    reference
        .lifetime
        .as_ref()
        .map(|lifetime| lifetime.ident.to_string())
        == expected.map(str::to_string)
}

fn str_slice_reference_type(
    item: &syn::Type,
    outer_lifetime: Option<&str>,
    inner_lifetime: Option<&str>,
) -> bool {
    let syn::Type::Reference(outer) = item else {
        return false;
    };
    let syn::Type::Slice(slice) = outer.elem.as_ref() else {
        return false;
    };
    let syn::Type::Reference(inner) = slice.elem.as_ref() else {
        return false;
    };
    outer.mutability.is_none()
        && inner.mutability.is_none()
        && lifetime_is(outer, outer_lifetime)
        && lifetime_is(inner, inner_lifetime)
        && type_is_named(inner.elem.as_ref(), "str")
}

fn plain_free_function_signature(signature: &syn::Signature) -> bool {
    signature.constness.is_none()
        && signature.asyncness.is_none()
        && signature.unsafety.is_none()
        && signature.abi.is_none()
        && signature.generics.params.is_empty()
        && signature.generics.where_clause.is_none()
        && signature.inputs.is_empty()
        && signature.variadic.is_none()
}

fn verify_exact_tests(
    source: &str,
    expected_functions: &[&str],
    error: &'static str,
) -> Result<(), &'static str> {
    let syntax = syn::parse_file(source).map_err(|_| error)?;
    for expected in expected_functions {
        let functions = syntax
            .items
            .iter()
            .filter_map(|item| match item {
                syn::Item::Fn(function) if function.sig.ident == *expected => Some(function),
                _ => None,
            })
            .collect::<Vec<_>>();
        if functions.len() != 1
            || !matches!(
                functions[0].attrs.as_slice(),
                [attribute]
                    if matches!(&attribute.meta, syn::Meta::Path(path) if path.is_ident("test"))
            )
        {
            return Err(error);
        }
    }
    Ok(())
}

pub(super) fn verify_normative_sanitizer_registry_edge(source: &str) -> Result<(), &'static str> {
    const ERROR: &str = "normative-sanitizer-edge";
    let syntax = syn::parse_file(source).map_err(|_| ERROR)?;
    let errors = syntax
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Enum(item) if item.ident == "NormativeContractError" => Some(item),
            _ => None,
        })
        .collect::<Vec<_>>();
    let [errors] = errors.as_slice() else {
        return Err(ERROR);
    };
    if errors.variants.len() != 2
        || errors.variants[0].ident != "Contract"
        || errors.variants[1].ident != "SanitizerReconciliation"
        || errors
            .variants
            .iter()
            .any(|variant| !matches!(variant.fields, syn::Fields::Unit))
    {
        return Err(ERROR);
    }

    let ordinary = unique_free_function(&syntax, "verify_normative_contract").ok_or(ERROR)?;
    let observed =
        unique_free_function(&syntax, "verify_normative_contract_observed").ok_or(ERROR)?;
    let inner = unique_free_function(&syntax, "verify_normative_contract_with").ok_or(ERROR)?;
    let boundary =
        unique_free_function(&syntax, "verify_sanitizer_registry_boundary").ok_or(ERROR)?;
    let reconciliation =
        unique_free_function(&syntax, "reconcile_sanitizer_registry_contract").ok_or(ERROR)?;
    if !wrapper_delegates(ordinary, true)
        || !wrapper_delegates(observed, false)
        || !inner_delegates_once(inner)
        || !boundary_delegates(boundary)
        || !reconciliation_completes_comparison(reconciliation)
    {
        return Err(ERROR);
    }
    Ok(())
}

fn unique_free_function<'a>(syntax: &'a syn::File, expected: &str) -> Option<&'a syn::ItemFn> {
    let mut functions = syntax.items.iter().filter_map(|item| match item {
        syn::Item::Fn(function) if function.sig.ident == expected => Some(function),
        _ => None,
    });
    let function = functions.next()?;
    functions.next().is_none().then_some(function)
}

fn path_is_bare_ident(expression: &syn::ExprPath, expected: &str) -> bool {
    expression.qself.is_none()
        && expression.path.leading_colon.is_none()
        && expression.path.segments.len() == 1
        && expression.path.is_ident(expected)
}

fn path_is_exact(expression: &syn::ExprPath, expected: &[&str]) -> bool {
    expression.qself.is_none() && simple_path_is(&expression.path, expected)
}

fn simple_path_is(path: &syn::Path, expected: &[&str]) -> bool {
    path.leading_colon.is_none()
        && path.segments.len() == expected.len()
        && path
            .segments
            .iter()
            .zip(expected)
            .all(|(segment, expected)| {
                segment.ident == *expected && matches!(segment.arguments, syn::PathArguments::None)
            })
}

fn call_path_is(call: &syn::ExprCall, expected: &[&str]) -> bool {
    matches!(call.func.as_ref(), syn::Expr::Path(path) if path_is_exact(path, expected))
}

fn wrapper_delegates(function: &syn::ItemFn, ordinary: bool) -> bool {
    let statements = function.block.stmts.as_slice();
    let call = match (ordinary, statements) {
        (
            true,
            [
                syn::Stmt::Local(local),
                syn::Stmt::Expr(syn::Expr::Call(call), None),
            ],
        ) if matches!(&local.pat, syn::Pat::Ident(pattern)
                if pattern.ident == "observer" && pattern.mutability.is_some()) =>
        {
            call
        }
        (false, [syn::Stmt::Expr(syn::Expr::Call(call), None)]) => call,
        _ => return false,
    };
    call_path_is(call, &["verify_normative_contract_with"])
        && call.args.len() == 5
        && matches!(&call.args[3], syn::Expr::Path(path)
            if path_is_bare_ident(path, "verify_sanitizer_registry_boundary"))
}

fn inner_delegates_once(function: &syn::ItemFn) -> bool {
    let statements = function.block.stmts.as_slice();
    let [_, _, _, delegated, completed] = statements else {
        return false;
    };
    let syn::Stmt::Expr(syn::Expr::Try(propagated), Some(_)) = delegated else {
        return false;
    };
    let syn::Expr::Call(call) = propagated.expr.as_ref() else {
        return false;
    };
    let syn::Stmt::Expr(syn::Expr::Call(completed), None) = completed else {
        return false;
    };
    call_path_is(call, &["sanitizer_verifier"])
        && call.args.len() == 3
        && call_path_is(completed, &["verify_normative_implementation"])
}

fn observer_stage(statement: &syn::Stmt, stage: &[&str]) -> bool {
    let syn::Stmt::Expr(syn::Expr::Call(call), Some(_)) = statement else {
        return false;
    };
    call_path_is(call, &["observer"])
        && matches!(call.args.iter().collect::<Vec<_>>().as_slice(), [syn::Expr::Path(path)]
            if path_is_exact(path, stage))
}

fn boundary_delegates(function: &syn::ItemFn) -> bool {
    let [invoked, delegated] = function.block.stmts.as_slice() else {
        return false;
    };
    let syn::Stmt::Expr(syn::Expr::Call(call), None) = delegated else {
        return false;
    };
    observer_stage(invoked, &["SanitizerStage", "BoundaryInvoked"])
        && call_path_is(call, &["reconcile_sanitizer_registry_contract"])
        && call.args.len() == 3
}

fn canonical_accessor_call(expression: &syn::Expr) -> bool {
    let syn::Expr::Call(call) = expression else {
        return false;
    };
    call_path_is(
        call,
        &[
            "crate",
            "source_bindings",
            "independent_sanitizer_only_paths",
        ],
    ) && call.args.is_empty()
}

fn plain_local_binding(statement: &syn::Stmt) -> Option<(&syn::Ident, &syn::Expr)> {
    let syn::Stmt::Local(local) = statement else {
        return None;
    };
    let syn::Pat::Ident(pattern) = &local.pat else {
        return None;
    };
    let initializer = local.init.as_ref()?;
    (local.attrs.is_empty()
        && pattern.by_ref.is_none()
        && pattern.mutability.is_none()
        && pattern.subpat.is_none()
        && initializer.diverge.is_none())
    .then_some((&pattern.ident, initializer.expr.as_ref()))
}

fn closure_projects_basename(expression: &syn::Expr) -> bool {
    let syn::Expr::Closure(closure) = expression else {
        return false;
    };
    let [syn::Pat::Ident(path_binding)] = closure.inputs.iter().collect::<Vec<_>>().as_slice()
    else {
        return false;
    };
    let syn::Expr::Block(body) = closure.body.as_ref() else {
        return false;
    };
    let [syn::Stmt::Expr(syn::Expr::MethodCall(ok_or), None)] = body.block.stmts.as_slice() else {
        return false;
    };
    let syn::Expr::MethodCall(filter) = ok_or.receiver.as_ref() else {
        return false;
    };
    let syn::Expr::MethodCall(next) = filter.receiver.as_ref() else {
        return false;
    };
    let syn::Expr::MethodCall(split) = next.receiver.as_ref() else {
        return false;
    };
    split.method == "rsplit"
        && matches!(split.receiver.as_ref(), syn::Expr::Path(path)
            if path_is_bare_ident(path, &path_binding.ident.to_string()))
        && matches!(split.args.iter().collect::<Vec<_>>().as_slice(),
            [syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Char(separator), .. })]
                if separator.value() == '/')
        && next.method == "next"
        && next.args.is_empty()
        && filter.method == "filter"
        && matches!(
            filter.args.iter().collect::<Vec<_>>().as_slice(),
            [syn::Expr::Closure(_)]
        )
        && ok_or.method == "ok_or"
        && matches!(ok_or.args.iter().collect::<Vec<_>>().as_slice(), [syn::Expr::Path(error)]
            if path_is_exact(error, &["NormativeContractError", "SanitizerReconciliation"]))
}

fn basename_projection_binding<'a>(
    statement: &'a syn::Stmt,
    authority_binding: &syn::Ident,
) -> Option<&'a syn::Ident> {
    let (binding, initializer) = plain_local_binding(statement)?;
    let syn::Expr::Try(propagated) = initializer else {
        return None;
    };
    let syn::Expr::MethodCall(collected) = propagated.expr.as_ref() else {
        return None;
    };
    let syn::Expr::MethodCall(mapped) = collected.receiver.as_ref() else {
        return None;
    };
    let syn::Expr::MethodCall(iterated) = mapped.receiver.as_ref() else {
        return None;
    };
    (collected.method == "collect"
        && collected.args.is_empty()
        && mapped.method == "map"
        && matches!(mapped.args.iter().collect::<Vec<_>>().as_slice(), [mapper]
            if closure_projects_basename(mapper))
        && iterated.method == "iter"
        && iterated.args.is_empty()
        && matches!(iterated.receiver.as_ref(), syn::Expr::Path(path)
            if path_is_bare_ident(path, &authority_binding.to_string())))
    .then_some(binding)
}

fn expression_is_binding(expression: &syn::Expr, binding: &str) -> bool {
    matches!(expression, syn::Expr::Path(path)
        if path_is_bare_ident(path, binding))
}

fn expression_references_binding(expression: &syn::Expr, binding: &syn::Ident) -> bool {
    matches!(expression, syn::Expr::Reference(reference)
        if reference.mutability.is_none()
            && expression_is_binding(reference.expr.as_ref(), &binding.to_string()))
}

fn propagated_reconciliation_call<'a>(
    expression: &'a syn::Expr,
    expected: &[&str],
) -> Option<&'a syn::ExprCall> {
    let syn::Expr::Try(propagated) = expression else {
        return None;
    };
    let syn::Expr::MethodCall(mapped) = propagated.expr.as_ref() else {
        return None;
    };
    let [syn::Expr::Closure(mapper)] = mapped.args.iter().collect::<Vec<_>>().as_slice() else {
        return None;
    };
    let syn::Expr::Call(call) = mapped.receiver.as_ref() else {
        return None;
    };
    (mapped.method == "map_err"
        && mapped.turbofish.is_none()
        && matches!(
            mapper.inputs.iter().collect::<Vec<_>>().as_slice(),
            [syn::Pat::Wild(_)]
        )
        && matches!(mapper.body.as_ref(), syn::Expr::Path(error)
            if path_is_exact(error, &["NormativeContractError", "SanitizerReconciliation"]))
        && call_path_is(call, expected))
    .then_some(call)
}

fn propagated_binding<'a>(
    statement: &'a syn::Stmt,
    callee: &[&str],
    argument: &str,
) -> Option<&'a syn::Ident> {
    let (binding, initializer) = plain_local_binding(statement)?;
    let call = propagated_reconciliation_call(initializer, callee)?;
    matches!(call.args.iter().collect::<Vec<_>>().as_slice(), [syn::Expr::Path(path)]
        if path_is_bare_ident(path, argument))
    .then_some(binding)
}

fn renderability_check(statement: &syn::Stmt, contract: &syn::Ident) -> bool {
    let syn::Stmt::Expr(syn::Expr::If(check), None) = statement else {
        return false;
    };
    matches!(check.cond.as_ref(), syn::Expr::Unary(negated)
        if matches!(negated.op, syn::UnOp::Not(_))
            && matches!(negated.expr.as_ref(), syn::Expr::Call(call)
                if call_path_is(call, &["contract_is_renderable"])
                    && matches!(call.args.iter().collect::<Vec<_>>().as_slice(), [argument]
                        if expression_references_binding(argument, contract))))
}

fn marker_check(statement: &syn::Stmt, contract: &syn::Ident) -> bool {
    let syn::Stmt::Expr(expression, Some(_)) = statement else {
        return false;
    };
    let Some(call) = propagated_reconciliation_call(expression, &["verify_marker_topology"]) else {
        return false;
    };
    matches!(call.args.iter().collect::<Vec<_>>().as_slice(),
        [syn::Expr::Path(document), contract_argument]
            if path_is_bare_ident(document, "document")
                && expression_references_binding(contract_argument, contract))
}

fn structured_sources_binding<'a>(
    statement: &'a syn::Stmt,
    contract: &syn::Ident,
) -> Option<&'a syn::Ident> {
    let syn::Stmt::Local(local) = statement else {
        return None;
    };
    let syn::Pat::TupleStruct(option) = &local.pat else {
        return None;
    };
    let [syn::Pat::Struct(binding)] = option.elems.iter().collect::<Vec<_>>().as_slice() else {
        return None;
    };
    let field = binding.fields.first()?;
    let (syn::Member::Named(member), syn::Pat::Ident(source)) = (&field.member, field.pat.as_ref())
    else {
        return None;
    };
    let initializer = local.init.as_ref()?;
    let syn::Expr::MethodCall(first) = initializer.expr.as_ref() else {
        return None;
    };
    let syn::Expr::Field(facts) = first.receiver.as_ref() else {
        return None;
    };
    (local.attrs.is_empty()
        && simple_path_is(&option.path, &["Some"])
        && simple_path_is(&binding.path, &["NormativeFact", "Bindings"])
        && binding.rest.is_some()
        && member == "sanitizer_sources"
        && source.by_ref.is_none()
        && source.mutability.is_none()
        && source.subpat.is_none()
        && initializer.diverge.is_some()
        && first.method == "first"
        && first.args.is_empty()
        && matches!(&facts.member, syn::Member::Named(member) if member == "facts")
        && expression_is_binding(facts.base.as_ref(), &contract.to_string()))
    .then_some(&source.ident)
}

fn comparison_local(
    statement: &syn::Stmt,
    documented: &syn::Ident,
    structured: &syn::Ident,
    projected: &syn::Ident,
) -> bool {
    let Some((pattern, initializer)) = plain_local_binding(statement) else {
        return false;
    };
    let syn::Expr::If(comparison) = initializer else {
        return false;
    };
    let syn::Expr::Binary(joined) = comparison.cond.as_ref() else {
        return false;
    };
    let (syn::Expr::Binary(documented_structured), syn::Expr::Binary(documented_projected)) =
        (joined.left.as_ref(), joined.right.as_ref())
    else {
        return false;
    };
    pattern == "comparison"
        && matches!(joined.op, syn::BinOp::And(_))
        && matches!(documented_structured.op, syn::BinOp::Eq(_))
        && expression_is_binding(documented_structured.left.as_ref(), &documented.to_string())
        && matches!(documented_structured.right.as_ref(), syn::Expr::Unary(dereference)
            if matches!(dereference.op, syn::UnOp::Deref(_))
                && expression_is_binding(dereference.expr.as_ref(), &structured.to_string()))
        && matches!(documented_projected.op, syn::BinOp::Eq(_))
        && expression_is_binding(documented_projected.left.as_ref(), &documented.to_string())
        && expression_is_binding(documented_projected.right.as_ref(), &projected.to_string())
        && comparison.else_branch.is_some()
        && matches!(comparison.then_branch.stmts.as_slice(),
            [syn::Stmt::Expr(syn::Expr::Path(path), None)]
                if path_is_exact(path, &["SanitizerComparison", "Match"]))
}

fn compared_stage(statement: &syn::Stmt) -> bool {
    let syn::Stmt::Expr(syn::Expr::Call(call), Some(_)) = statement else {
        return false;
    };
    let [syn::Expr::Call(stage)] = call.args.iter().collect::<Vec<_>>().as_slice() else {
        return false;
    };
    call_path_is(call, &["observer"])
        && call_path_is(stage, &["SanitizerStage", "Compared"])
        && matches!(stage.args.iter().collect::<Vec<_>>().as_slice(), [syn::Expr::Path(path)]
            if path_is_bare_ident(path, "comparison"))
}

fn reconciliation_completes_comparison(function: &syn::ItemFn) -> bool {
    let [
        started,
        contract,
        renderable,
        markers,
        structured,
        documented,
        authority,
        projection,
        comparison,
        observed,
        syn::Stmt::Expr(syn::Expr::Match(completed), None),
    ] = function.block.stmts.as_slice()
    else {
        return false;
    };
    let Some(contract_binding) =
        propagated_binding(contract, &["load_normative_contract"], "build")
    else {
        return false;
    };
    let Some(structured_sources) = structured_sources_binding(structured, contract_binding) else {
        return false;
    };
    let Some(documented_sources) =
        propagated_binding(documented, &["documented_sanitizer_sources"], "document")
    else {
        return false;
    };
    let Some((authority_binding, authority_initializer)) = plain_local_binding(authority) else {
        return false;
    };
    if !canonical_accessor_call(authority_initializer) {
        return false;
    }
    let Some(projected_sources) = basename_projection_binding(projection, authority_binding) else {
        return false;
    };
    observer_stage(started, &["SanitizerStage", "ReconciliationStarted"])
        && renderability_check(renderable, contract_binding)
        && marker_check(markers, contract_binding)
        && comparison_local(
            comparison,
            documented_sources,
            structured_sources,
            projected_sources,
        )
        && compared_stage(observed)
        && matches!(completed.expr.as_ref(), syn::Expr::Path(path)
            if path_is_bare_ident(path, "comparison"))
        && completed.arms.len() == 2
}
