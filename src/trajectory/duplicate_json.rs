use crate::LegitimacyError;
use serde::de::{DeserializeSeed, MapAccess, SeqAccess, Visitor};
use serde::{Deserialize, Deserializer};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use super::{MAX_JSON_KEY_BYTES_PER_OBJECT_V0, MAX_JSON_KEYS_PER_OBJECT_V0};

pub(super) fn deserialize_unique_map<'de, D, V>(
    deserializer: D,
) -> Result<BTreeMap<String, V>, D::Error>
where
    D: Deserializer<'de>,
    V: Deserialize<'de>,
{
    struct UniqueMapVisitor<V>(std::marker::PhantomData<V>);

    impl<'de, V> Visitor<'de> for UniqueMapVisitor<V>
    where
        V: Deserialize<'de>,
    {
        type Value = BTreeMap<String, V>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("a map without duplicate keys")
        }

        fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
        where
            A: MapAccess<'de>,
        {
            let mut values = BTreeMap::new();
            while let Some(key) = map.next_key::<String>()? {
                if values.contains_key(&key) {
                    return Err(serde::de::Error::custom("duplicate JSON object key"));
                }
                let value = map.next_value::<V>()?;
                values.insert(key, value);
            }
            Ok(values)
        }
    }

    deserializer.deserialize_map(UniqueMapVisitor(std::marker::PhantomData))
}

pub(super) fn reject_duplicate_json_keys(
    input: &[u8],
    context: &str,
) -> Result<JsonRootKind, LegitimacyError> {
    scan_json_with_limits(input, context, JsonScanLimits::unbounded())
        .map_err(JsonScanError::into_source)
}

#[derive(Clone, Copy)]
pub(super) struct JsonScanLimits {
    pub max_depth: usize,
    pub max_nodes: usize,
    pub max_total_keys: usize,
    pub max_decoded_string_bytes: usize,
}

impl JsonScanLimits {
    const fn unbounded() -> Self {
        Self {
            max_depth: usize::MAX,
            max_nodes: usize::MAX,
            max_total_keys: usize::MAX,
            max_decoded_string_bytes: usize::MAX,
        }
    }
}

pub(super) fn scan_json_with_limits(
    input: &[u8],
    context: &str,
    limits: JsonScanLimits,
) -> Result<JsonRootKind, JsonScanError> {
    let mut deserializer = serde_json::Deserializer::from_slice(input);
    let state = RefCell::new(ScanState::new(limits));
    let result = ScanSeed {
        state: &state,
        depth: 1,
    }
    .deserialize(&mut deserializer)
    .and_then(|scanned| {
        deserializer.end()?;
        Ok(scanned)
    });
    result.map_err(|source| {
        let source = LegitimacyError::Json {
            context: context.to_string(),
            source,
        };
        if state.borrow().budget_exceeded {
            JsonScanError::Budget(source)
        } else {
            JsonScanError::Invalid(source)
        }
    })
}

pub(super) enum JsonScanError {
    Invalid(LegitimacyError),
    Budget(LegitimacyError),
}

impl JsonScanError {
    fn into_source(self) -> LegitimacyError {
        match self {
            Self::Invalid(source) | Self::Budget(source) => source,
        }
    }

    pub const fn is_budget(&self) -> bool {
        matches!(self, Self::Budget(_))
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum JsonRootKind {
    Object,
    NonObject,
}

struct ScanState {
    limits: JsonScanLimits,
    nodes: usize,
    total_keys: usize,
    decoded_string_bytes: usize,
    budget_exceeded: bool,
}

impl ScanState {
    const fn new(limits: JsonScanLimits) -> Self {
        Self {
            limits,
            nodes: 0,
            total_keys: 0,
            decoded_string_bytes: 0,
            budget_exceeded: false,
        }
    }

    fn enter_node<E: serde::de::Error>(&mut self, depth: usize) -> Result<(), E> {
        if depth > self.limits.max_depth {
            return self.budget_error("JSON nesting depth limit exceeded");
        }
        self.nodes = match self.nodes.checked_add(1) {
            Some(nodes) => nodes,
            None => return self.budget_error("JSON node count overflow"),
        };
        if self.nodes > self.limits.max_nodes {
            return self.budget_error("JSON node count limit exceeded");
        }
        Ok(())
    }

    fn add_string<E: serde::de::Error>(&mut self, bytes: usize) -> Result<(), E> {
        self.decoded_string_bytes = match self.decoded_string_bytes.checked_add(bytes) {
            Some(decoded_string_bytes) => decoded_string_bytes,
            None => return self.budget_error("decoded JSON string byte count overflow"),
        };
        if self.decoded_string_bytes > self.limits.max_decoded_string_bytes {
            return self.budget_error("decoded JSON string byte limit exceeded");
        }
        Ok(())
    }

    fn add_key<E: serde::de::Error>(&mut self, bytes: usize) -> Result<(), E> {
        self.total_keys = match self.total_keys.checked_add(1) {
            Some(total_keys) => total_keys,
            None => return self.budget_error("JSON key count overflow"),
        };
        if self.total_keys > self.limits.max_total_keys {
            return self.budget_error("JSON total key count limit exceeded");
        }
        self.add_string(bytes)
    }

    fn next_depth<E: serde::de::Error>(&mut self, depth: usize) -> Result<usize, E> {
        match depth.checked_add(1) {
            Some(next) => Ok(next),
            None => self.budget_error("JSON nesting depth overflow"),
        }
    }

    fn budget_error<T, E: serde::de::Error>(&mut self, message: &'static str) -> Result<T, E> {
        self.budget_exceeded = true;
        Err(E::custom(message))
    }
}

struct ScanSeed<'a> {
    state: &'a RefCell<ScanState>,
    depth: usize,
}

impl<'de> DeserializeSeed<'de> for ScanSeed<'_> {
    type Value = JsonRootKind;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        self.state.borrow_mut().enter_node::<D::Error>(self.depth)?;
        deserializer.deserialize_any(StreamingJsonVisitor {
            state: self.state,
            depth: self.depth,
        })
    }
}

struct StreamingJsonVisitor<'a> {
    state: &'a RefCell<ScanState>,
    depth: usize,
}

impl<'de> Visitor<'de> for StreamingJsonVisitor<'_> {
    type Value = JsonRootKind;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("JSON without duplicate object keys")
    }

    fn visit_bool<E>(self, _value: bool) -> Result<Self::Value, E> {
        Ok(JsonRootKind::NonObject)
    }

    fn visit_i64<E>(self, _value: i64) -> Result<Self::Value, E> {
        Ok(JsonRootKind::NonObject)
    }

    fn visit_u64<E>(self, _value: u64) -> Result<Self::Value, E> {
        Ok(JsonRootKind::NonObject)
    }

    fn visit_f64<E>(self, value: f64) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        if value.is_finite() {
            Ok(JsonRootKind::NonObject)
        } else {
            Err(E::custom("non-finite JSON number"))
        }
    }

    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        self.state.borrow_mut().add_string::<E>(value.len())?;
        Ok(JsonRootKind::NonObject)
    }

    fn visit_string<E>(self, value: String) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        self.state.borrow_mut().add_string::<E>(value.len())?;
        Ok(JsonRootKind::NonObject)
    }

    fn visit_none<E>(self) -> Result<Self::Value, E> {
        Ok(JsonRootKind::NonObject)
    }

    fn visit_unit<E>(self) -> Result<Self::Value, E> {
        Ok(JsonRootKind::NonObject)
    }

    fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let depth = self.state.borrow_mut().next_depth::<A::Error>(self.depth)?;
        while sequence
            .next_element_seed(ScanSeed {
                state: self.state,
                depth,
            })?
            .is_some()
        {}
        Ok(JsonRootKind::NonObject)
    }

    fn visit_map<A>(self, mut object: A) -> Result<Self::Value, A::Error>
    where
        A: MapAccess<'de>,
    {
        let mut keys = BTreeSet::new();
        let mut key_count = 0usize;
        let mut key_bytes = 0usize;
        while let Some(key) = object.next_key::<String>()? {
            if keys.contains(&key) {
                return Err(serde::de::Error::custom("duplicate JSON object key"));
            }
            key_count = match key_count.checked_add(1) {
                Some(key_count) => key_count,
                None => {
                    return self
                        .state
                        .borrow_mut()
                        .budget_error("JSON object key count overflow");
                }
            };
            if key_count > MAX_JSON_KEYS_PER_OBJECT_V0 {
                return self
                    .state
                    .borrow_mut()
                    .budget_error("JSON object key count exceeds v0 limit of 1024");
            }
            key_bytes = match key_bytes.checked_add(key.len()) {
                Some(key_bytes) => key_bytes,
                None => {
                    return self
                        .state
                        .borrow_mut()
                        .budget_error("JSON object key byte count overflow");
                }
            };
            if key_bytes > MAX_JSON_KEY_BYTES_PER_OBJECT_V0 {
                return self
                    .state
                    .borrow_mut()
                    .budget_error("JSON object key bytes exceed v0 limit of 65536");
            }
            self.state.borrow_mut().add_key::<A::Error>(key.len())?;
            keys.insert(key);
            let depth = self.state.borrow_mut().next_depth::<A::Error>(self.depth)?;
            object.next_value_seed(ScanSeed {
                state: self.state,
                depth,
            })?;
        }
        Ok(JsonRootKind::Object)
    }
}
