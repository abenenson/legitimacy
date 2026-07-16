use regex::Regex;
use serde_json::Value;
use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};

#[derive(Clone, Debug)]
struct PatternRecord {
    fixture: String,
    pattern: String,
}

#[derive(Clone, Debug)]
struct ParityCase {
    fixture: String,
    pattern: String,
    input: String,
    expected: bool,
}

fn unique_path(label: &str, extension: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    std::env::temp_dir().join(format!("legitimacy-{label}-{nanos}.{extension}"))
}

fn collect_patterns(value: &Value, patterns: &mut BTreeSet<String>) {
    match value {
        Value::Object(map) => {
            for (key, child) in map {
                if key == "ContentMatch"
                    && let Value::Object(content_match) = child
                    && let Some(Value::String(pattern)) = content_match.get("regex")
                {
                    patterns.insert(pattern.clone());
                }
                collect_patterns(child, patterns);
            }
        }
        Value::Array(items) => {
            for item in items {
                collect_patterns(item, patterns);
            }
        }
        Value::Null | Value::Bool(_) | Value::Number(_) | Value::String(_) => {}
    }
}

fn fixture_patterns(path: &Path, fixture: &str) -> Vec<PatternRecord> {
    let value: Value = serde_json::from_slice(&fs::read(path).unwrap()).unwrap();
    let mut patterns = BTreeSet::new();
    collect_patterns(&value, &mut patterns);
    patterns
        .into_iter()
        .map(|pattern| PatternRecord {
            fixture: fixture.to_string(),
            pattern,
        })
        .collect()
}

fn graph_fixture_paths(root: &Path) -> Vec<PathBuf> {
    let mut fixtures = Vec::new();
    let mut stack = vec![root.to_path_buf()];

    while let Some(path) = stack.pop() {
        let entries = fs::read_dir(&path)
            .unwrap_or_else(|error| panic!("failed to read {}: {error}", path.display()));
        for entry in entries {
            let entry = entry.unwrap();
            let entry_path = entry.path();
            if entry_path.is_dir() {
                stack.push(entry_path);
                continue;
            }
            if entry_path
                .file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.ends_with("-graph.json"))
            {
                fixtures.push(entry_path);
            }
        }
    }

    fixtures.sort();
    fixtures
}

fn all_patterns() -> Vec<PatternRecord> {
    graph_fixture_paths(Path::new("audits"))
        .into_iter()
        .flat_map(|fixture_path| {
            let fixture = fixture_path
                .strip_prefix("audits")
                .unwrap()
                .display()
                .to_string();
            fixture_patterns(&fixture_path, &fixture)
        })
        .collect()
}

fn literal_pattern_target(pattern: &str) -> Result<String, String> {
    let mut output = String::with_capacity(pattern.len());
    let mut chars = pattern.chars();
    while let Some(ch) = chars.next() {
        if ch == '\\' {
            let escaped = chars
                .next()
                .ok_or_else(|| format!("trailing backslash in pattern {pattern:?}"))?;
            output.push(escaped);
            continue;
        }

        if matches!(
            ch,
            '^' | '$' | '|' | '.' | '(' | ')' | '[' | ']' | '{' | '}' | '*' | '+' | '?'
        ) {
            return Err(format!(
                "pattern uses active regex operator {ch:?}; update Lean parity before shipping"
            ));
        }

        output.push(ch);
    }
    Ok(output)
}

fn mutate_non_match(target: &str) -> String {
    let mut chars = target.chars().collect::<Vec<_>>();
    assert!(
        !chars.is_empty(),
        "ContentMatch pattern unexpectedly synthesized an empty target"
    );

    let index = chars.len() / 2;
    chars[index] = if chars[index] == '\u{2603}' {
        'X'
    } else {
        '\u{2603}'
    };
    chars.into_iter().collect()
}

fn parity_cases() -> Vec<ParityCase> {
    let mut cases = Vec::new();

    for record in all_patterns() {
        let target = literal_pattern_target(&record.pattern).unwrap_or_else(|error| {
            panic!(
                "fixture {} pattern {:?} is outside the shipped literal-only surface: {}",
                record.fixture, record.pattern, error
            )
        });

        let regex = Regex::new(&record.pattern).unwrap();
        let embedded = format!("prefix::{target}::suffix");
        let mutated = mutate_non_match(&target);

        let target_expected = regex.is_match(&target);
        let embedded_expected = regex.is_match(&embedded);
        let mutated_expected = regex.is_match(&mutated);

        assert!(
            target_expected,
            "fixture {} pattern {:?} failed to match its synthesized literal target {:?}",
            record.fixture, record.pattern, target
        );
        assert!(
            embedded_expected,
            "fixture {} pattern {:?} failed substring match on {:?}",
            record.fixture, record.pattern, embedded
        );
        assert!(
            !mutated_expected,
            "fixture {} pattern {:?} unexpectedly matched mutated negative {:?}",
            record.fixture, record.pattern, mutated
        );

        cases.push(ParityCase {
            fixture: record.fixture.clone(),
            pattern: record.pattern.clone(),
            input: target,
            expected: target_expected,
        });
        cases.push(ParityCase {
            fixture: record.fixture.clone(),
            pattern: record.pattern.clone(),
            input: embedded,
            expected: embedded_expected,
        });
        cases.push(ParityCase {
            fixture: record.fixture,
            pattern: record.pattern,
            input: mutated,
            expected: mutated_expected,
        });
    }

    cases
}

fn lean_string_literal(input: &str) -> String {
    let mut output = String::with_capacity(input.len() + 2);
    output.push('"');
    for ch in input.chars() {
        match ch {
            '\\' => output.push_str("\\\\"),
            '"' => output.push_str("\\\""),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            _ => output.push(ch),
        }
    }
    output.push('"');
    output
}

fn lean_results(cases: &[ParityCase]) -> Vec<Option<bool>> {
    let script_path = unique_path("content-match-regex-parity", "lean");
    let case_lines = cases
        .iter()
        .map(|case| {
            format!(
                "  ({}, {})",
                lean_string_literal(&case.pattern),
                lean_string_literal(&case.input)
            )
        })
        .collect::<Vec<_>>()
        .join(",\n");

    let script = format!(
        "import Legitimacy.Regex\n\nopen Legitimacy\n\n\
def cases : List (String × String) := [\n{case_lines}\n]\n\n\
def renderResult (value : Option Bool) : String :=\n\
  match value with\n\
  | some true => \"some:true\"\n\
  | some false => \"some:false\"\n\
  | none => \"none\"\n\n\
def main : IO Unit := do\n\
  for entry in cases do\n\
    IO.println <| renderResult <| Regex.matchesSource? entry.1 entry.2\n"
    );

    fs::write(&script_path, script).unwrap();

    let output = Command::new("lake")
        .current_dir(Path::new(env!("CARGO_MANIFEST_DIR")).join("lean"))
        .args(["env", "lean", "--run", script_path.to_str().unwrap()])
        .output()
        .unwrap();

    if script_path.exists() {
        fs::remove_file(&script_path).unwrap();
    }

    assert!(
        output.status.success(),
        "Lean parity runner failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .map(|line| match line {
            "some:true" => Some(true),
            "some:false" => Some(false),
            "none" => None,
            other => panic!("unexpected Lean parity output line: {other}"),
        })
        .collect()
}

fn lean_parity_preflight() -> bool {
    const LEAN_TOOLCHAIN_MISSING: &str = "Lean toolchain missing; install elan/lake to run this test. See https://lean-lang.org/lean4/doc/setup.html";
    const LEAN_BUILD_MISSING: &str = "Lean Legitimacy not built; run 'cd lean && lake build Legitimacy' first, then re-run this test.";

    if !Command::new("lake")
        .arg("--version")
        .status()
        .is_ok_and(|status| status.success())
    {
        eprintln!("{LEAN_TOOLCHAIN_MISSING}");
        return false;
    }

    let legitimacy_olean = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("lean")
        .join(".lake/build/lib/lean/Legitimacy.olean");
    if !legitimacy_olean.exists() {
        eprintln!("{LEAN_BUILD_MISSING}");
        return false;
    }

    true
}

#[test]
fn committed_graph_content_match_patterns_match_lean_regex_port() {
    if !lean_parity_preflight() {
        return;
    }

    let cases = parity_cases();
    let lean_results = lean_results(&cases);

    assert_eq!(
        lean_results.len(),
        cases.len(),
        "Lean parity runner returned {} rows for {} cases",
        lean_results.len(),
        cases.len()
    );

    for (case, lean_result) in cases.iter().zip(lean_results) {
        let lean_result = lean_result.unwrap_or_else(|| {
            panic!(
                "Lean regex parser rejected fixture {} pattern {:?}",
                case.fixture, case.pattern
            )
        });

        assert_eq!(
            case.expected, lean_result,
            "Rust/Lean regex parity drift for fixture {} pattern {:?} input {:?}",
            case.fixture, case.pattern, case.input
        );
    }
}
