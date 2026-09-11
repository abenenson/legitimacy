use serde::de::{DeserializeSeed, MapAccess, SeqAccess, Visitor};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

pub(crate) const EXACT_RUSTC_VV: &[u8] = b"rustc 1.95.0-nightly (9e79395f9 2026-02-10)\n\
binary: rustc\n\
commit-hash: 9e79395f92bff6a8f536430e42a4beae69f60ff8\n\
commit-date: 2026-02-10\n\
host: x86_64-unknown-linux-gnu\n\
release: 1.95.0-nightly\n\
LLVM version: 22.1.0\n";

pub(crate) const EXACT_CARGO_VV: &[u8] = b"cargo 1.95.0-nightly (fe2f314ae 2026-01-30)\n\
release: 1.95.0-nightly\n\
commit-hash: fe2f314aef06e688a9517da1ac0577bb1854d01f\n\
commit-date: 2026-01-30\n\
host: x86_64-unknown-linux-gnu\n\
libgit2: 1.9.2 (sys:0.20.3 vendored)\n\
libcurl: 8.15.0-DEV (sys:0.4.83+curl-8.15.0 vendored ssl:OpenSSL/3.5.4)\n\
ssl: OpenSSL 3.5.4 30 Sep 2025\n\
os: Ubuntu 24.4.0 (noble) [64-bit]\n";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ProtocolFailure {
    CompilerIdentity,
    CargoProtocol,
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum UniqueValue {
    Null,
    Bool(bool),
    Number(String),
    String(String),
    Array(Vec<UniqueValue>),
    Object(BTreeMap<String, UniqueValue>),
}

impl UniqueValue {
    pub(crate) fn object(&self) -> Result<&BTreeMap<String, UniqueValue>, ProtocolFailure> {
        match self {
            Self::Object(value) => Ok(value),
            _ => Err(ProtocolFailure::CargoProtocol),
        }
    }

    pub(crate) fn string(&self) -> Result<&str, ProtocolFailure> {
        match self {
            Self::String(value) => Ok(value),
            _ => Err(ProtocolFailure::CargoProtocol),
        }
    }

    pub(crate) fn bool(&self) -> Result<bool, ProtocolFailure> {
        match self {
            Self::Bool(value) => Ok(*value),
            _ => Err(ProtocolFailure::CargoProtocol),
        }
    }

    pub(crate) fn array(&self) -> Result<&[UniqueValue], ProtocolFailure> {
        match self {
            Self::Array(value) => Ok(value),
            _ => Err(ProtocolFailure::CargoProtocol),
        }
    }

    fn nullable_string(&self) -> Result<Option<&str>, ProtocolFailure> {
        match self {
            Self::Null => Ok(None),
            Self::String(value) => Ok(Some(value)),
            _ => Err(ProtocolFailure::CargoProtocol),
        }
    }

    fn unsigned(&self) -> Result<u64, ProtocolFailure> {
        match self {
            Self::Number(value) => value.parse().map_err(|_| ProtocolFailure::CargoProtocol),
            _ => Err(ProtocolFailure::CargoProtocol),
        }
    }
}

struct UniqueSeed;

impl<'de> DeserializeSeed<'de> for UniqueSeed {
    type Value = UniqueValue;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_any(UniqueVisitor)
    }
}

struct UniqueVisitor;

impl<'de> Visitor<'de> for UniqueVisitor {
    type Value = UniqueValue;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a JSON value without duplicate object keys")
    }

    fn visit_bool<E>(self, value: bool) -> Result<Self::Value, E> {
        Ok(UniqueValue::Bool(value))
    }

    fn visit_i64<E>(self, value: i64) -> Result<Self::Value, E> {
        Ok(UniqueValue::Number(value.to_string()))
    }

    fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E> {
        Ok(UniqueValue::Number(value.to_string()))
    }

    fn visit_f64<E>(self, value: f64) -> Result<Self::Value, E> {
        Ok(UniqueValue::Number(value.to_string()))
    }

    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(UniqueValue::String(value.to_string()))
    }

    fn visit_string<E>(self, value: String) -> Result<Self::Value, E> {
        Ok(UniqueValue::String(value))
    }

    fn visit_none<E>(self) -> Result<Self::Value, E> {
        Ok(UniqueValue::Null)
    }

    fn visit_unit<E>(self) -> Result<Self::Value, E> {
        Ok(UniqueValue::Null)
    }

    fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let mut values = Vec::new();
        while let Some(value) = sequence.next_element_seed(UniqueSeed)? {
            values.push(value);
        }
        Ok(UniqueValue::Array(values))
    }

    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
    where
        A: MapAccess<'de>,
    {
        let mut values = BTreeMap::new();
        while let Some(key) = map.next_key::<String>()? {
            if values.contains_key(&key) {
                return Err(serde::de::Error::custom("duplicate object key"));
            }
            let value = map.next_value_seed(UniqueSeed)?;
            values.insert(key, value);
        }
        Ok(UniqueValue::Object(values))
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CargoProtocolEvidence {
    pub(crate) raw_digest: [u8; 32],
    pub(crate) selected_lines: Vec<Vec<u8>>,
    pub(crate) records: Vec<CargoRecord>,
    pub(crate) terminal_success: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum CargoRecord {
    CompilerArtifact {
        raw: Vec<u8>,
        package_id: String,
        manifest_path: String,
        target: CargoTarget,
        profile: CargoProfile,
        features: Vec<String>,
        filenames: Vec<String>,
        executable: Option<String>,
        fresh: bool,
    },
    CompilerMessage,
    BuildScriptExecuted {
        raw: Vec<u8>,
        package_id: String,
        linked_libs: Vec<String>,
        linked_paths: Vec<String>,
        cfgs: Vec<String>,
        environment: Vec<(String, String)>,
        out_dir: String,
    },
    BuildFinished,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CargoTarget {
    pub(crate) kinds: Vec<String>,
    pub(crate) crate_types: Vec<String>,
    pub(crate) name: String,
    pub(crate) src_path: String,
    pub(crate) edition: String,
    pub(crate) doc: bool,
    pub(crate) doctest: bool,
    pub(crate) test: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CargoProfile {
    pub(crate) opt_level: String,
    pub(crate) debuginfo: Option<u64>,
    pub(crate) debug_assertions: bool,
    pub(crate) overflow_checks: bool,
    pub(crate) test: bool,
}

pub(crate) fn validate_compiler_identity(bytes: &[u8]) -> Result<(), ProtocolFailure> {
    if bytes == EXACT_RUSTC_VV {
        Ok(())
    } else {
        Err(ProtocolFailure::CompilerIdentity)
    }
}

pub(crate) fn validate_cargo_identity(bytes: &[u8]) -> Result<(), ProtocolFailure> {
    if bytes == EXACT_CARGO_VV {
        Ok(())
    } else {
        Err(ProtocolFailure::CargoProtocol)
    }
}

pub(crate) fn parse_cargo_stream(
    bytes: &[u8],
    cargo_success: bool,
) -> Result<CargoProtocolEvidence, ProtocolFailure> {
    if bytes.is_empty() || !bytes.ends_with(b"\n") || bytes.contains(&b'\r') {
        return Err(ProtocolFailure::CargoProtocol);
    }
    let mut selected_lines = Vec::new();
    let mut records = Vec::new();
    let mut terminal = None;
    for raw in bytes.split_inclusive(|byte| *byte == b'\n') {
        if terminal.is_some() {
            return Err(ProtocolFailure::CargoProtocol);
        }
        if raw.len() > 1024 * 1024 {
            return Err(ProtocolFailure::CargoProtocol);
        }
        let line = &raw[..raw.len() - 1];
        let value = parse_unique(line)?;
        let object = value.object()?;
        let reason = exact_field(object, "reason")?.string()?;
        match reason {
            "compiler-artifact" => {
                let record = parse_artifact(object, raw)?;
                selected_lines.push(raw.to_vec());
                records.push(record);
            }
            "build-script-executed" => {
                let record = parse_build_script(object, raw)?;
                selected_lines.push(raw.to_vec());
                records.push(record);
            }
            "compiler-message" => {
                require_keys(
                    object,
                    &["manifest_path", "message", "package_id", "reason", "target"],
                )?;
                exact_field(object, "package_id")?.string()?;
                exact_field(object, "manifest_path")?.string()?;
                exact_field(object, "message")?.object()?;
                parse_target(exact_field(object, "target")?)?;
                records.push(CargoRecord::CompilerMessage);
            }
            "build-finished" => {
                require_keys(object, &["reason", "success"])?;
                terminal = Some(exact_field(object, "success")?.bool()?);
                records.push(CargoRecord::BuildFinished);
            }
            _ => return Err(ProtocolFailure::CargoProtocol),
        }
    }
    let terminal_success = terminal.ok_or(ProtocolFailure::CargoProtocol)?;
    if terminal_success != cargo_success {
        return Err(ProtocolFailure::CargoProtocol);
    }
    Ok(CargoProtocolEvidence {
        raw_digest: Sha256::digest(bytes).into(),
        selected_lines,
        records,
        terminal_success,
    })
}

pub(crate) fn parse_unique(bytes: &[u8]) -> Result<UniqueValue, ProtocolFailure> {
    let text = std::str::from_utf8(bytes).map_err(|_| ProtocolFailure::CargoProtocol)?;
    let mut deserializer = serde_json::Deserializer::from_str(text);
    let value = UniqueSeed
        .deserialize(&mut deserializer)
        .map_err(|_| ProtocolFailure::CargoProtocol)?;
    deserializer
        .end()
        .map_err(|_| ProtocolFailure::CargoProtocol)?;
    Ok(value)
}

fn parse_artifact(
    object: &BTreeMap<String, UniqueValue>,
    raw: &[u8],
) -> Result<CargoRecord, ProtocolFailure> {
    require_keys(
        object,
        &[
            "executable",
            "features",
            "filenames",
            "fresh",
            "manifest_path",
            "package_id",
            "profile",
            "reason",
            "target",
        ],
    )?;
    Ok(CargoRecord::CompilerArtifact {
        raw: raw.to_vec(),
        package_id: exact_field(object, "package_id")?.string()?.to_string(),
        manifest_path: exact_field(object, "manifest_path")?.string()?.to_string(),
        target: parse_target(exact_field(object, "target")?)?,
        profile: parse_profile(exact_field(object, "profile")?)?,
        features: string_array(exact_field(object, "features")?)?,
        filenames: string_array(exact_field(object, "filenames")?)?,
        executable: exact_field(object, "executable")?
            .nullable_string()?
            .map(str::to_string),
        fresh: exact_field(object, "fresh")?.bool()?,
    })
}

fn parse_build_script(
    object: &BTreeMap<String, UniqueValue>,
    raw: &[u8],
) -> Result<CargoRecord, ProtocolFailure> {
    require_keys(
        object,
        &[
            "cfgs",
            "env",
            "linked_libs",
            "linked_paths",
            "out_dir",
            "package_id",
            "reason",
        ],
    )?;
    let mut environment = Vec::new();
    let mut names = BTreeSet::new();
    for pair in exact_field(object, "env")?.array()? {
        let pair = pair.array()?;
        if pair.len() != 2 {
            return Err(ProtocolFailure::CargoProtocol);
        }
        let name = pair[0].string()?.to_string();
        let value = pair[1].string()?.to_string();
        if !names.insert(name.clone()) {
            return Err(ProtocolFailure::CargoProtocol);
        }
        environment.push((name, value));
    }
    Ok(CargoRecord::BuildScriptExecuted {
        raw: raw.to_vec(),
        package_id: exact_field(object, "package_id")?.string()?.to_string(),
        linked_libs: string_array(exact_field(object, "linked_libs")?)?,
        linked_paths: string_array(exact_field(object, "linked_paths")?)?,
        cfgs: string_array(exact_field(object, "cfgs")?)?,
        environment,
        out_dir: exact_field(object, "out_dir")?.string()?.to_string(),
    })
}

fn parse_target(value: &UniqueValue) -> Result<CargoTarget, ProtocolFailure> {
    let object = value.object()?;
    require_keys(
        object,
        &[
            "crate_types",
            "doc",
            "doctest",
            "edition",
            "kind",
            "name",
            "src_path",
            "test",
        ],
    )?;
    let kinds = string_array(exact_field(object, "kind")?)?;
    let crate_types = string_array(exact_field(object, "crate_types")?)?;
    if kinds.is_empty() || crate_types.is_empty() {
        return Err(ProtocolFailure::CargoProtocol);
    }
    Ok(CargoTarget {
        kinds,
        crate_types,
        name: exact_field(object, "name")?.string()?.to_string(),
        src_path: exact_field(object, "src_path")?.string()?.to_string(),
        edition: exact_field(object, "edition")?.string()?.to_string(),
        doc: exact_field(object, "doc")?.bool()?,
        doctest: exact_field(object, "doctest")?.bool()?,
        test: exact_field(object, "test")?.bool()?,
    })
}

fn parse_profile(value: &UniqueValue) -> Result<CargoProfile, ProtocolFailure> {
    let object = value.object()?;
    require_keys(
        object,
        &[
            "debug_assertions",
            "debuginfo",
            "opt_level",
            "overflow_checks",
            "test",
        ],
    )?;
    let debuginfo = match exact_field(object, "debuginfo")? {
        UniqueValue::Null => None,
        value => Some(value.unsigned()?),
    };
    Ok(CargoProfile {
        opt_level: exact_field(object, "opt_level")?.string()?.to_string(),
        debuginfo,
        debug_assertions: exact_field(object, "debug_assertions")?.bool()?,
        overflow_checks: exact_field(object, "overflow_checks")?.bool()?,
        test: exact_field(object, "test")?.bool()?,
    })
}

fn string_array(value: &UniqueValue) -> Result<Vec<String>, ProtocolFailure> {
    value
        .array()?
        .iter()
        .map(|value| value.string().map(str::to_string))
        .collect()
}

fn exact_field<'a>(
    object: &'a BTreeMap<String, UniqueValue>,
    name: &str,
) -> Result<&'a UniqueValue, ProtocolFailure> {
    object.get(name).ok_or(ProtocolFailure::CargoProtocol)
}

fn require_keys(
    object: &BTreeMap<String, UniqueValue>,
    keys: &[&str],
) -> Result<(), ProtocolFailure> {
    let expected = keys.iter().copied().collect::<BTreeSet<_>>();
    let actual = object.keys().map(String::as_str).collect::<BTreeSet<_>>();
    if actual == expected {
        Ok(())
    } else {
        Err(ProtocolFailure::CargoProtocol)
    }
}

pub(crate) fn assert_compiler_protocol_fixtures_are_strict_and_deterministic() {
    assert_eq!(validate_compiler_identity(EXACT_RUSTC_VV), Ok(()));
    assert_eq!(validate_cargo_identity(EXACT_CARGO_VV), Ok(()));
    let mut changed = EXACT_RUSTC_VV.to_vec();
    changed.push(b'\n');
    assert_eq!(
        validate_compiler_identity(&changed),
        Err(ProtocolFailure::CompilerIdentity)
    );
    let stream = concat!(
        "{\"reason\":\"compiler-artifact\",\"package_id\":\"path+file:///case#legitimacy@1.0.0\",\"manifest_path\":\"/case/Cargo.toml\",\"target\":{\"kind\":[\"lib\"],\"crate_types\":[\"lib\"],\"name\":\"legitimacy\",\"src_path\":\"/case/src/lib.rs\",\"edition\":\"2024\",\"doc\":true,\"doctest\":true,\"test\":true},\"profile\":{\"opt_level\":\"0\",\"debuginfo\":2,\"debug_assertions\":true,\"overflow_checks\":true,\"test\":false},\"features\":[],\"filenames\":[],\"executable\":null,\"fresh\":false}\n",
        "{\"reason\":\"build-script-executed\",\"package_id\":\"path+file:///case#legitimacy@1.0.0\",\"linked_libs\":[],\"linked_paths\":[],\"cfgs\":[],\"env\":[],\"out_dir\":\"/target/build/out\"}\n",
        "{\"reason\":\"compiler-message\",\"package_id\":\"dep\",\"manifest_path\":\"/dep/Cargo.toml\",\"target\":{\"kind\":[\"lib\"],\"crate_types\":[\"lib\"],\"name\":\"dep\",\"src_path\":\"/dep/src/lib.rs\",\"edition\":\"2024\",\"doc\":true,\"doctest\":true,\"test\":true},\"message\":{}}\n",
        "{\"reason\":\"build-finished\",\"success\":true}\n"
    );
    let evidence = parse_cargo_stream(stream.as_bytes(), true).unwrap();
    assert!(evidence.terminal_success);
    assert_eq!(evidence.selected_lines.len(), 2);
    assert_eq!(evidence.records.len(), 4);
    assert_eq!(evidence.raw_digest, Sha256::digest(stream.as_bytes())[..]);
    for hostile in [
        "{\"reason\":\"build-finished\",\"reason\":\"build-finished\",\"success\":true}\n",
        "{\"reason\":\"unknown\"}\n{\"reason\":\"build-finished\",\"success\":true}\n",
        "{\"reason\":\"build-finished\",\"success\":true}\n{\"reason\":\"compiler-message\",\"package_id\":\"x\",\"message\":{}}\n",
        "{\"reason\":\"build-finished\",\"success\":\"true\"}\n",
        "{\"reason\":\"compiler-message\",\"package_id\":\"x\",\"message\":{}}\n{\"reason\":\"build-finished\",\"success\":true}\n",
        "{\"reason\":\"compiler-artifact\",\"package_id\":\"x\",\"manifest_path\":\"/x/Cargo.toml\",\"target\":{\"kind\":[],\"crate_types\":[],\"name\":\"x\",\"src_path\":\"/x/lib.rs\",\"edition\":\"2024\",\"doc\":true,\"doctest\":true,\"test\":true},\"profile\":{\"opt_level\":\"0\",\"debuginfo\":2,\"debug_assertions\":true,\"overflow_checks\":true,\"test\":false},\"features\":[],\"filenames\":[],\"executable\":null,\"fresh\":false}\n{\"reason\":\"build-finished\",\"success\":true}\n",
    ] {
        assert_eq!(
            parse_cargo_stream(hostile.as_bytes(), true),
            Err(ProtocolFailure::CargoProtocol)
        );
    }
}
