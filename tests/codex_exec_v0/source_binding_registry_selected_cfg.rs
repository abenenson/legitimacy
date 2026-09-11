use std::collections::{BTreeMap, BTreeSet};
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::{Attribute, Lit, Meta, Token};

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum CfgAtom {
    Flag(String),
    KeyValue(String, String),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ActiveCfgAtoms(BTreeSet<CfgAtom>);

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct RecognizedCfgEntry {
    allows_flag: bool,
    values: BTreeSet<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct RecognizedCfgGrammar(BTreeMap<String, RecognizedCfgEntry>);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum CfgFailure {
    CfgEvidence,
    RecognizedCfgGrammar,
    UnsupportedCfgPredicate,
}

impl ActiveCfgAtoms {
    pub(crate) fn parse(bytes: &[u8]) -> Result<Self, CfgFailure> {
        if bytes.is_empty() || !bytes.ends_with(b"\n") || bytes.contains(&b'\r') {
            return Err(CfgFailure::CfgEvidence);
        }
        let text = std::str::from_utf8(bytes).map_err(|_| CfgFailure::CfgEvidence)?;
        let mut atoms = BTreeSet::new();
        for line in text.lines() {
            let atom = if let Some((name, value)) = line.split_once('=') {
                let name = normalized_ident(name).ok_or(CfgFailure::CfgEvidence)?;
                let literal =
                    syn::parse_str::<syn::LitStr>(value).map_err(|_| CfgFailure::CfgEvidence)?;
                CfgAtom::KeyValue(name, literal.value())
            } else {
                CfgAtom::Flag(normalized_ident(line).ok_or(CfgFailure::CfgEvidence)?)
            };
            if !atoms.insert(atom) {
                return Err(CfgFailure::CfgEvidence);
            }
        }
        Ok(Self(atoms))
    }
}

impl RecognizedCfgGrammar {
    pub(crate) fn parse(bytes: &[u8]) -> Result<Self, CfgFailure> {
        if bytes.is_empty() || !bytes.ends_with(b"\n") || bytes.contains(&b'\r') {
            return Err(CfgFailure::RecognizedCfgGrammar);
        }
        let text = std::str::from_utf8(bytes).map_err(|_| CfgFailure::RecognizedCfgGrammar)?;
        let mut entries = BTreeMap::new();
        for line in text.lines() {
            let meta =
                syn::parse_str::<Meta>(line).map_err(|_| CfgFailure::RecognizedCfgGrammar)?;
            let Meta::List(outer) = meta else {
                return Err(CfgFailure::RecognizedCfgGrammar);
            };
            if !outer.path.is_ident("cfg") {
                return Err(CfgFailure::RecognizedCfgGrammar);
            }
            let arguments = syn::parse2::<CheckCfgArguments>(outer.tokens)
                .map_err(|_| CfgFailure::RecognizedCfgGrammar)?;
            let name = normalize_ident(&arguments.name);
            let mut allows_flag = false;
            let mut values = BTreeSet::new();
            let mut prior_value = None;
            for expression in arguments.values {
                match expression {
                    syn::Expr::Lit(expression) => {
                        let Lit::Str(value) = expression.lit else {
                            return Err(CfgFailure::RecognizedCfgGrammar);
                        };
                        let value = value.value();
                        if prior_value.as_ref().is_some_and(|prior| prior >= &value)
                            || !values.insert(value.clone())
                        {
                            return Err(CfgFailure::RecognizedCfgGrammar);
                        }
                        prior_value = Some(value);
                    }
                    syn::Expr::Call(call)
                        if call.args.is_empty()
                            && matches!(
                                call.func.as_ref(),
                                syn::Expr::Path(path) if path.path.is_ident("none")
                            ) =>
                    {
                        if allows_flag {
                            return Err(CfgFailure::RecognizedCfgGrammar);
                        }
                        allows_flag = true;
                    }
                    _ => return Err(CfgFailure::RecognizedCfgGrammar),
                }
            }
            if entries
                .insert(
                    name,
                    RecognizedCfgEntry {
                        allows_flag,
                        values,
                    },
                )
                .is_some()
            {
                return Err(CfgFailure::RecognizedCfgGrammar);
            }
        }
        Ok(Self(entries))
    }

    pub(crate) fn evaluate(
        &self,
        active: &ActiveCfgAtoms,
        predicate: &Meta,
    ) -> Result<bool, CfgFailure> {
        match predicate {
            Meta::Path(path) => {
                let name = single_ident(path)?;
                let entry = self
                    .0
                    .get(&name)
                    .ok_or(CfgFailure::UnsupportedCfgPredicate)?;
                if !entry.allows_flag {
                    return Err(CfgFailure::UnsupportedCfgPredicate);
                }
                Ok(active.0.contains(&CfgAtom::Flag(name)))
            }
            Meta::NameValue(value) => {
                let name = single_ident(&value.path)?;
                let syn::Expr::Lit(expression) = &value.value else {
                    return Err(CfgFailure::UnsupportedCfgPredicate);
                };
                let Lit::Str(value) = &expression.lit else {
                    return Err(CfgFailure::UnsupportedCfgPredicate);
                };
                let value = value.value();
                let entry = self
                    .0
                    .get(&name)
                    .ok_or(CfgFailure::UnsupportedCfgPredicate)?;
                if !entry.values.contains(&value) {
                    return Err(CfgFailure::UnsupportedCfgPredicate);
                }
                Ok(active.0.contains(&CfgAtom::KeyValue(name, value)))
            }
            Meta::List(list) if list.path.is_ident("all") || list.path.is_ident("any") => {
                let nested = list
                    .parse_args_with(Punctuated::<Meta, Token![,]>::parse_terminated)
                    .map_err(|_| CfgFailure::UnsupportedCfgPredicate)?;
                let mut values = Vec::new();
                for predicate in nested {
                    values.push(self.evaluate(active, &predicate)?);
                }
                Ok(if list.path.is_ident("all") {
                    values.into_iter().all(|value| value)
                } else {
                    values.into_iter().any(|value| value)
                })
            }
            Meta::List(list) if list.path.is_ident("not") => {
                let nested = list
                    .parse_args_with(Punctuated::<Meta, Token![,]>::parse_terminated)
                    .map_err(|_| CfgFailure::UnsupportedCfgPredicate)?;
                if nested.len() != 1 {
                    return Err(CfgFailure::UnsupportedCfgPredicate);
                }
                Ok(!self.evaluate(active, nested.first().unwrap())?)
            }
            _ => Err(CfgFailure::UnsupportedCfgPredicate),
        }
    }

    pub(crate) fn retained_attributes(
        &self,
        active: &ActiveCfgAtoms,
        attributes: &[Attribute],
    ) -> Result<Option<Vec<Meta>>, CfgFailure> {
        let mut expanded = Vec::new();
        for attribute in attributes {
            expand_attribute_meta(self, active, attribute.meta.clone(), &mut expanded)?;
        }
        for meta in &expanded {
            if let Meta::List(list) = meta
                && list.path.is_ident("cfg")
            {
                let predicate = syn::parse2::<Meta>(list.tokens.clone())
                    .map_err(|_| CfgFailure::UnsupportedCfgPredicate)?;
                if !self.evaluate(active, &predicate)? {
                    return Ok(None);
                }
            }
        }
        Ok(Some(expanded))
    }
}

fn expand_attribute_meta(
    grammar: &RecognizedCfgGrammar,
    active: &ActiveCfgAtoms,
    meta: Meta,
    expanded: &mut Vec<Meta>,
) -> Result<(), CfgFailure> {
    if let Meta::List(list) = &meta
        && list.path.is_ident("cfg_attr")
    {
        let arguments = syn::parse2::<CfgAttrArguments>(list.tokens.clone())
            .map_err(|_| CfgFailure::UnsupportedCfgPredicate)?;
        if grammar.evaluate(active, &arguments.predicate)? {
            for nested in arguments.attributes {
                expand_attribute_meta(grammar, active, nested, expanded)?;
            }
        }
    } else {
        expanded.push(meta);
    }
    Ok(())
}

struct CheckCfgArguments {
    name: syn::Ident,
    values: Punctuated<syn::Expr, Token![,]>,
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

impl Parse for CheckCfgArguments {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let name = input.parse()?;
        input.parse::<Token![,]>()?;
        let values_name: syn::Ident = input.parse()?;
        if values_name != "values" {
            return Err(input.error("expected values"));
        }
        let content;
        syn::parenthesized!(content in input);
        let values = content.parse_terminated(syn::Expr::parse, Token![,])?;
        if !input.is_empty() {
            return Err(input.error("trailing check-cfg input"));
        }
        Ok(Self { name, values })
    }
}

fn single_ident(path: &syn::Path) -> Result<String, CfgFailure> {
    if path.leading_colon.is_some() || path.segments.len() != 1 {
        return Err(CfgFailure::UnsupportedCfgPredicate);
    }
    Ok(normalize_ident(&path.segments[0].ident))
}

fn normalized_ident(value: &str) -> Option<String> {
    let ident = syn::parse_str::<syn::Ident>(value).ok()?;
    (ident == value).then(|| normalize_ident(&ident))
}

fn normalize_ident(ident: &syn::Ident) -> String {
    let spelling = ident.to_string();
    spelling.strip_prefix("r#").unwrap_or(&spelling).to_string()
}

pub(crate) fn assert_selected_cfg_uses_active_atoms_and_recognized_false_grammar() {
    let active =
        ActiveCfgAtoms::parse(b"debug_assertions\ntarget_arch=\"x86_64\"\ntarget_os=\"linux\"\n")
            .unwrap();
    let grammar = RecognizedCfgGrammar::parse(
        b"cfg(debug_assertions, values(none()))\n\
cfg(target_arch, values(\"aarch64\", \"x86_64\"))\n\
cfg(target_os, values(\"linux\", \"windows\"))\n",
    )
    .unwrap();
    assert!(
        grammar
            .evaluate(&active, &syn::parse_str("target_os = \"linux\"").unwrap())
            .unwrap()
    );
    assert!(
        !grammar
            .evaluate(&active, &syn::parse_str("target_os = \"windows\"").unwrap())
            .unwrap()
    );
    assert!(
        grammar
            .evaluate(
                &active,
                &syn::parse_str("all(debug_assertions, not(target_os = \"windows\"))").unwrap()
            )
            .unwrap()
    );
    assert_eq!(
        grammar.evaluate(&active, &syn::parse_str("invented = \"linux\"").unwrap()),
        Err(CfgFailure::UnsupportedCfgPredicate)
    );
    assert_eq!(
        RecognizedCfgGrammar::parse(
            b"cfg(target_os, values(\"linux\"))\ncfg(target_os, values(\"windows\"))\n"
        ),
        Err(CfgFailure::RecognizedCfgGrammar)
    );
    assert_eq!(
        RecognizedCfgGrammar::parse(b"cfg(target_os, values(\"windows\", \"linux\"))\n"),
        Err(CfgFailure::RecognizedCfgGrammar)
    );
}
