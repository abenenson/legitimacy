use super::ParsedFunction;
use crate::GovernanceGraph;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct BoundaryCausalSafetyAssessment {
    pub summary: String,
    pub affected_governance_nodes: usize,
    pub external_dependency_count: usize,
    pub ungoverned_dependencies: Vec<UngovernedDependency>,
}

impl Default for BoundaryCausalSafetyAssessment {
    fn default() -> Self {
        Self {
            summary:
                "0 governance nodes have 0 transitive external dependencies not in the governance graph (causal boundary analysis)"
                    .to_string(),
            affected_governance_nodes: 0,
            external_dependency_count: 0,
            ungoverned_dependencies: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct UngovernedDependency {
    pub governance_node: String,
    pub dependency: String,
}

pub(crate) fn assess_boundary_causal_safety(
    graph: &GovernanceGraph,
    parsed: &[ParsedFunction],
) -> BoundaryCausalSafetyAssessment {
    let governance_ids = graph
        .nodes
        .keys()
        .map(ToString::to_string)
        .collect::<BTreeSet<_>>();
    let governance_names = parsed
        .iter()
        .filter(|function| governance_ids.contains(&function.id))
        .map(|function| function.function_name.as_str())
        .collect::<BTreeSet<_>>();
    let function_names = parsed
        .iter()
        .map(|function| function.function_name.as_str())
        .collect::<BTreeSet<_>>();
    let parsed_by_id = parsed
        .iter()
        .map(|function| (function.id.as_str(), function))
        .collect::<BTreeMap<_, _>>();
    let mut parsed_by_name = BTreeMap::<&str, Vec<&ParsedFunction>>::new();
    for function in parsed {
        parsed_by_name
            .entry(function.function_name.as_str())
            .or_default()
            .push(function);
    }

    let mut dependencies = BTreeSet::<(String, String)>::new();
    for governance_id in &governance_ids {
        let Some(function) = parsed_by_id.get(governance_id.as_str()) else {
            continue;
        };
        let mut seen = BTreeSet::new();
        let mut stack = direct_dependencies(function, &function_names)
            .into_iter()
            .collect::<Vec<_>>();
        while let Some(dependency) = stack.pop() {
            if !seen.insert(dependency.clone()) {
                continue;
            }
            if !governance_names.contains(dependency.as_str()) {
                dependencies.insert((governance_id.clone(), dependency.clone()));
            }
            if let Some(next_functions) = parsed_by_name.get(dependency.as_str()) {
                for next_function in next_functions {
                    stack.extend(direct_dependencies(next_function, &function_names));
                }
            }
        }
    }

    let affected_governance_nodes = dependencies
        .iter()
        .map(|(node, _)| node)
        .collect::<BTreeSet<_>>()
        .len();
    let external_dependency_count = dependencies.len();
    let summary = format!(
        "{affected_governance_nodes} governance nodes have {external_dependency_count} transitive external dependencies not in the governance graph (causal boundary analysis)"
    );
    let ungoverned_dependencies = dependencies
        .into_iter()
        .map(|(governance_node, dependency)| UngovernedDependency {
            governance_node,
            dependency,
        })
        .collect();

    BoundaryCausalSafetyAssessment {
        summary,
        affected_governance_nodes,
        external_dependency_count,
        ungoverned_dependencies,
    }
}

fn direct_dependencies(
    function: &ParsedFunction,
    function_names: &BTreeSet<&str>,
) -> BTreeSet<String> {
    let mut dependencies = function
        .calls
        .iter()
        .filter(|dependency| {
            *dependency != &function.function_name && !is_low_signal_dependency(dependency)
        })
        .cloned()
        .collect::<BTreeSet<_>>();
    dependencies.extend(
        function
            .callback_refs
            .iter()
            .filter(|dependency: &&String| {
                function_names.contains(dependency.as_str())
                    && !is_low_signal_dependency(dependency)
            })
            .cloned(),
    );
    dependencies
}

fn is_low_signal_dependency(dependency: &str) -> bool {
    matches!(
        dependency,
        "as_ref"
            | "clone"
            | "contains"
            | "contains_key"
            | "get"
            | "insert"
            | "is_empty"
            | "iter"
            | "len"
            | "map"
            | "new"
            | "ok_or_else"
            | "push"
            | "to_string"
            | "unwrap"
            | "unwrap_or"
            | "unwrap_or_default"
    )
}
