//! Parser for Claude Code `.claude/` project configuration directories.
//!
//! Out of scope for v0.1: Bash-hook body semantic analysis, `.lsp.json`
//! server parsing, `CLAUDE.md` instruction parsing, and enterprise managed
//! settings overlays.

use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
};

use gray_matter::{Matter, engine::YAML};
use serde::{Deserialize, Deserializer};
use serde_json::Value;

use crate::{
    Decision, EdgeTransform, Gate, GateLogic, GovernanceGraph, GovernanceNode, GraphBuilder,
    LegitimacyError, NodeId,
};

pub fn parse_claude_dir(path: &Path) -> Result<GovernanceGraph, LegitimacyError> {
    let metadata = fs::metadata(path).map_err(|source| LegitimacyError::Io {
        context: format!("Claude directory '{}'", path.display()),
        source,
    })?;
    if !metadata.is_dir() {
        return Err(LegitimacyError::invalid_input(format!(
            "Claude directory parser requires a directory, got '{}'",
            path.display()
        )));
    }

    let mut graph = ClaudeGraph::default();
    parse_settings_file(&mut graph, &path.join("settings.json"))?;
    parse_settings_file(&mut graph, &path.join("hooks").join("hooks.json"))?;
    parse_skills_dir(&mut graph, &path.join("skills"))?;
    parse_agents_dir(&mut graph, &path.join("agents"))?;
    graph.build()
}

#[derive(Default)]
struct ClaudeGraph {
    nodes: BTreeMap<String, GovernanceNode>,
    edges: Vec<(String, String)>,
}

impl ClaudeGraph {
    fn add_binary_node(&mut self, id: String, name: String, gates: Vec<Gate>, default: Decision) {
        self.nodes
            .entry(id.clone())
            .or_insert_with(|| GovernanceNode::Binary {
                id: NodeId::new(id).expect("generated node id is non-empty"),
                name,
                gates,
                default,
                combination: GateLogic::FirstMatch,
            });
    }

    fn add_tool_node(&mut self, tool: &str) {
        let label = normalize_label(tool);
        self.add_binary_node(
            format!("tool:{label}"),
            tool.to_string(),
            vec![Gate::ExactMatch {
                value: tool.to_string(),
                decision: Decision::Permit,
            }],
            Decision::Deny,
        );
    }

    fn add_edge(&mut self, from: String, to: String) {
        if from != to
            && !self
                .edges
                .iter()
                .any(|edge| edge == &(from.clone(), to.clone()))
        {
            self.edges.push((from, to));
        }
    }

    fn build(self) -> Result<GovernanceGraph, LegitimacyError> {
        let mut builder = GraphBuilder::new()?;
        for node in self.nodes.into_values() {
            builder = builder.add_node(node)?;
        }
        for (from, to) in self.edges {
            builder = builder.add_edge(
                NodeId::new(from)?,
                NodeId::new(to)?,
                EdgeTransform::PassThrough,
            )?;
        }
        builder.build()
    }
}

#[derive(Debug, Default, Deserialize)]
struct ClaudeSettings {
    #[serde(default)]
    permissions: ClaudePermissions,
    #[serde(default)]
    hooks: Value,
}

#[derive(Debug, Default, Deserialize)]
struct ClaudePermissions {
    #[serde(default, deserialize_with = "deserialize_string_list")]
    allow: Vec<String>,
    #[serde(default, deserialize_with = "deserialize_string_list")]
    deny: Vec<String>,
    #[serde(default, deserialize_with = "deserialize_string_list")]
    ask: Vec<String>,
}

#[derive(Debug, Default, Deserialize)]
struct SkillFrontMatter {
    name: Option<String>,
    #[serde(
        default,
        rename = "allowed-tools",
        alias = "allowedTools",
        deserialize_with = "deserialize_string_list"
    )]
    allowed_tools: Vec<String>,
    #[serde(default)]
    context: Option<String>,
    #[serde(default)]
    agent: Option<String>,
}

#[derive(Debug, Default, Deserialize)]
#[serde(rename_all = "camelCase")]
struct AgentFrontMatter {
    name: Option<String>,
    #[serde(default, deserialize_with = "deserialize_string_list")]
    tools: Vec<String>,
    #[serde(default, deserialize_with = "deserialize_string_list")]
    disallowed_tools: Vec<String>,
    #[serde(default, deserialize_with = "deserialize_string_list")]
    preloaded_skills: Vec<String>,
    #[serde(default)]
    max_turns: Option<u64>,
    #[serde(default)]
    model: Option<String>,
    #[serde(default)]
    hooks: Option<Value>,
}

fn parse_settings_file(graph: &mut ClaudeGraph, path: &Path) -> Result<(), LegitimacyError> {
    if !path.exists() {
        return Ok(());
    }
    let settings: ClaudeSettings = read_json(path)?;
    parse_permissions(graph, path, &settings.permissions)?;
    parse_hooks_value(graph, path, &settings.hooks);
    Ok(())
}

fn parse_permissions(
    graph: &mut ClaudeGraph,
    path: &Path,
    permissions: &ClaudePermissions,
) -> Result<(), LegitimacyError> {
    for (field, decision, matchers) in [
        ("allow", Decision::Permit, &permissions.allow),
        ("deny", Decision::Deny, &permissions.deny),
        ("ask", Decision::Escalate, &permissions.ask),
    ] {
        for (index, matcher) in matchers.iter().enumerate() {
            let id = format!(
                "permission:{field}:{}:{index}",
                normalize_label(path.display().to_string())
            );
            graph.add_binary_node(
                id.clone(),
                format!("{field} {matcher}"),
                vec![gate_for_matcher(matcher, decision.clone())],
                Decision::Deny,
            );
            graph.add_tool_node(matcher);
            graph.add_edge(id, format!("tool:{}", normalize_label(matcher)));
        }
    }
    Ok(())
}

fn parse_hooks_value(graph: &mut ClaudeGraph, path: &Path, hooks: &Value) {
    let Some(events) = hooks.as_object() else {
        return;
    };
    for (event, entries) in events {
        for (index, entry) in hook_entries(entries).iter().enumerate() {
            let matcher = entry
                .get("matcher")
                .or_else(|| entry.get("tool"))
                .or_else(|| entry.get("toolName"))
                .and_then(Value::as_str)
                .unwrap_or(event);
            let id = format!(
                "hook:{}:{}:{index}",
                normalize_label(event),
                normalize_label(path.display().to_string())
            );
            graph.add_binary_node(
                id.clone(),
                format!("{event} hook {matcher}"),
                vec![gate_for_matcher(matcher, Decision::Permit)],
                Decision::Deny,
            );
            graph.add_tool_node(matcher);
            graph.add_edge(id, format!("tool:{}", normalize_label(matcher)));
        }
    }
}

fn hook_entries(value: &Value) -> Vec<Value> {
    if let Some(entries) = value.as_array() {
        return entries.clone();
    }
    if value.is_object() {
        return vec![value.clone()];
    }
    Vec::new()
}

fn parse_skills_dir(graph: &mut ClaudeGraph, skills_dir: &Path) -> Result<(), LegitimacyError> {
    if !skills_dir.exists() {
        return Ok(());
    }
    for path in markdown_files(skills_dir)? {
        let frontmatter = read_frontmatter::<SkillFrontMatter>(&path)?;
        let name = frontmatter
            .name
            .clone()
            .or_else(|| path.parent().and_then(file_name_string))
            .unwrap_or_else(|| "skill".to_string());
        let skill_id = format!("skill:{}", normalize_label(&name));
        graph.add_binary_node(skill_id.clone(), name, Vec::new(), Decision::Permit);
        for tool in &frontmatter.allowed_tools {
            graph.add_tool_node(tool);
            graph.add_edge(skill_id.clone(), format!("tool:{}", normalize_label(tool)));
        }
        if frontmatter.context.as_deref() == Some("fork")
            && let Some(agent) = frontmatter.agent.as_deref()
        {
            let agent_id = format!("subagent:{}", normalize_label(agent));
            graph.add_binary_node(
                agent_id.clone(),
                agent.to_string(),
                Vec::new(),
                Decision::Permit,
            );
            graph.add_edge(skill_id, agent_id);
        }
    }
    Ok(())
}

fn parse_agents_dir(graph: &mut ClaudeGraph, agents_dir: &Path) -> Result<(), LegitimacyError> {
    if !agents_dir.exists() {
        return Ok(());
    }
    for path in markdown_files(agents_dir)? {
        let frontmatter = read_frontmatter::<AgentFrontMatter>(&path)?;
        let name = frontmatter
            .name
            .clone()
            .or_else(|| {
                path.file_stem()
                    .and_then(|name| name.to_str())
                    .map(ToString::to_string)
            })
            .unwrap_or_else(|| "subagent".to_string());
        let agent_id = format!("subagent:{}", normalize_label(&name));
        let mut gates = Vec::new();
        if let Some(model) = frontmatter.model {
            gates.push(Gate::ExactMatch {
                value: format!("model:{model}"),
                decision: Decision::Permit,
            });
        }
        if let Some(max_turns) = frontmatter.max_turns {
            gates.push(Gate::ThresholdGate {
                field: "maxTurns".to_string(),
                min: max_turns as f64,
                decision: Decision::Permit,
            });
        }
        for tool in &frontmatter.disallowed_tools {
            gates.push(gate_for_matcher(tool, Decision::Deny));
        }
        if frontmatter.hooks.is_some() {
            gates.push(Gate::ContentMatch {
                regex: "hooks".to_string(),
                decision: Decision::Deny,
            });
        }
        graph.add_binary_node(agent_id.clone(), name, gates, Decision::Permit);
        for tool in &frontmatter.tools {
            graph.add_tool_node(tool);
            graph.add_edge(agent_id.clone(), format!("tool:{}", normalize_label(tool)));
        }
        for skill in &frontmatter.preloaded_skills {
            let skill_id = format!("skill:{}", normalize_label(skill));
            graph.add_binary_node(
                skill_id.clone(),
                skill.to_string(),
                Vec::new(),
                Decision::Permit,
            );
            graph.add_edge(agent_id.clone(), skill_id);
        }
    }
    Ok(())
}

fn read_json<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T, LegitimacyError> {
    let input = fs::read_to_string(path).map_err(|source| LegitimacyError::Io {
        context: format!("reading '{}'", path.display()),
        source,
    })?;
    serde_json::from_str(&input).map_err(|source| LegitimacyError::Json {
        context: path.display().to_string(),
        source,
    })
}

fn read_frontmatter<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T, LegitimacyError> {
    let input = fs::read_to_string(path).map_err(|source| LegitimacyError::Io {
        context: format!("reading '{}'", path.display()),
        source,
    })?;
    let matter = Matter::<YAML>::new();
    let parsed = matter.parse::<T>(&input).map_err(|source| {
        LegitimacyError::invalid_input(format!("{}: {source}", path.display()))
    })?;
    parsed.data.ok_or_else(|| {
        LegitimacyError::invalid_input(format!(
            "Markdown file '{}' is missing YAML frontmatter",
            path.display()
        ))
    })
}

fn markdown_files(dir: &Path) -> Result<Vec<PathBuf>, LegitimacyError> {
    let mut files = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(current) = stack.pop() {
        let mut entries = fs::read_dir(&current)
            .map_err(|source| LegitimacyError::Io {
                context: format!("directory '{}'", current.display()),
                source,
            })?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|source| LegitimacyError::Io {
                context: format!("directory '{}'", current.display()),
                source,
            })?;
        entries.sort_by_key(|entry| entry.path());
        for entry in entries {
            let path = entry.path();
            let file_type = entry.file_type().map_err(|source| LegitimacyError::Io {
                context: format!("directory entry '{}'", path.display()),
                source,
            })?;
            if file_type.is_dir() {
                stack.push(path);
            } else if file_type.is_file()
                && path.extension().and_then(|extension| extension.to_str()) == Some("md")
            {
                files.push(path);
            }
        }
    }
    files.sort();
    Ok(files)
}

fn gate_for_matcher(matcher: &str, decision: Decision) -> Gate {
    if let Some(regex) = matcher.strip_prefix("regex:") {
        Gate::ContentMatch {
            regex: regex.to_string(),
            decision,
        }
    } else if let Some(prefix) = matcher.split('*').next()
        && matcher.contains('*')
        && !prefix.is_empty()
    {
        Gate::PrefixMatch {
            pattern: prefix.to_string(),
            decision,
        }
    } else {
        Gate::ExactMatch {
            value: matcher.to_string(),
            decision,
        }
    }
}

fn normalize_label(value: impl AsRef<str>) -> String {
    let normalized = value
        .as_ref()
        .chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() || matches!(ch, '-' | '_' | ':' | '.') {
                ch.to_ascii_lowercase()
            } else {
                '-'
            }
        })
        .collect::<String>();
    let trimmed = normalized.trim_matches('-');
    if trimmed.is_empty() {
        "unnamed".to_string()
    } else {
        trimmed.to_string()
    }
}

fn file_name_string(path: &Path) -> Option<String> {
    path.file_name()
        .and_then(|name| name.to_str())
        .map(ToString::to_string)
}

fn deserialize_string_list<'de, D>(deserializer: D) -> Result<Vec<String>, D::Error>
where
    D: Deserializer<'de>,
{
    #[derive(Deserialize)]
    #[serde(untagged)]
    enum StringList {
        One(String),
        Many(Vec<String>),
    }

    let Some(value) = Option::<StringList>::deserialize(deserializer)? else {
        return Ok(Vec::new());
    };
    let values = match value {
        StringList::One(value) => value
            .split(',')
            .map(str::trim)
            .filter(|value| !value.is_empty())
            .map(ToString::to_string)
            .collect(),
        StringList::Many(values) => values,
    };
    Ok(values)
}
