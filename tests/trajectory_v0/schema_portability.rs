use super::*;

#[test]
fn schema_numeric_maxima_match_portable_operational_ceilings() {
    let schema: Value =
        serde_json::from_slice(legitimacy::trajectory::TRAJECTORY_SCHEMA_BYTES_V0).unwrap();
    assert!(
        jsonschema::draft202012::meta::is_valid(&schema),
        "embedded schema must satisfy the Draft 2020-12 meta-schema"
    );
    let validator = jsonschema::draft202012::new(&schema).unwrap();

    let expected = BTreeMap::from([
        (
            "/$defs/evidenced_index/properties/value/maximum".to_string(),
            (
                (legitimacy::trajectory::MAX_EVENTS_V0 - 1) as u64,
                "/events/0/sequence_index/value",
            ),
        ),
        (
            "/$defs/raw_capture_seal/properties/record_count/maximum".to_string(),
            (
                legitimacy::trajectory::MAX_RAW_RECORDS_V0 as u64,
                "/raw_capture/record_count",
            ),
        ),
        (
            "/$defs/raw_record_reference/properties/record_index/maximum".to_string(),
            (
                (legitimacy::trajectory::MAX_RAW_RECORDS_V0 - 1) as u64,
                "/events/0/raw_record/record_index",
            ),
        ),
        (
            "/$defs/source_locator/properties/byte_length/maximum".to_string(),
            (
                legitimacy::trajectory::MAX_RAW_RECORD_BYTES_V0 as u64,
                "/events/0/event_id/evidence/locator/byte_length",
            ),
        ),
        (
            "/$defs/source_locator/properties/byte_offset/maximum".to_string(),
            (
                legitimacy::trajectory::MAX_RAW_RECORD_BYTES_V0 as u64 - 1,
                "/events/0/event_id/evidence/locator/byte_offset",
            ),
        ),
        (
            "/$defs/source_locator/properties/record_index/maximum".to_string(),
            (
                (legitimacy::trajectory::MAX_RAW_RECORDS_V0 - 1) as u64,
                "/events/0/event_id/evidence/locator/record_index",
            ),
        ),
    ]);
    let mut actual = BTreeMap::new();
    collect_numeric_maxima(&schema, "", &mut actual);
    assert_eq!(
        actual.keys().collect::<BTreeSet<_>>(),
        expected.keys().collect::<BTreeSet<_>>(),
        "all schema numeric maxima must be explicitly bound to v0 operational ceilings"
    );

    let raw = vec![RECORD_ZERO];
    let (trace, _) = fixture(&raw);
    let good = serde_json::to_value(trace).unwrap();
    for (schema_pointer, (ceiling, instance_pointer)) in expected {
        assert_eq!(
            schema.pointer(&schema_pointer).and_then(Value::as_u64),
            Some(ceiling),
            "wrong operational ceiling at {schema_pointer}"
        );

        let mut at_ceiling = good.clone();
        *at_ceiling.pointer_mut(instance_pointer).unwrap() = json!(ceiling);
        assert!(
            validator.is_valid(&at_ceiling),
            "{instance_pointer} must accept its operational ceiling {ceiling}"
        );

        let mut above_ceiling = good.clone();
        *above_ceiling.pointer_mut(instance_pointer).unwrap() = json!(ceiling + 1);
        assert!(
            !validator.is_valid(&above_ceiling),
            "{instance_pointer} must reject one above its operational ceiling {ceiling}"
        );
    }
}

#[test]
fn all_schema_numeric_bounds_are_ieee_754_interoperable() {
    let schema: Value =
        serde_json::from_slice(legitimacy::trajectory::TRAJECTORY_SCHEMA_BYTES_V0).unwrap();
    assert_interoperable_numeric_bounds(&schema, "");
}

#[test]
fn schema_is_a_structural_prescreen_for_integer_number_tokens() {
    let schema: Value =
        serde_json::from_slice(legitimacy::trajectory::TRAJECTORY_SCHEMA_BYTES_V0).unwrap();
    let validator = jsonschema::draft202012::new(&schema).unwrap();
    let raw = vec![RECORD_ZERO];
    let (trace, _) = fixture(&raw);
    let encoded = serde_json::to_string(&trace).unwrap();
    let decimal = encoded.replacen("\"record_count\":1", "\"record_count\":1.0", 1);
    let exponent = encoded.replacen("\"record_count\":1", "\"record_count\":1e0", 1);

    for wire in [decimal, exponent] {
        let value: Value = serde_json::from_str(&wire).unwrap();
        assert!(
            validator.is_valid(&value),
            "JSON Schema mathematical integers include equivalent decimal/exponent tokens"
        );
        assert!(
            TrajectoryTraceV0::from_json_slice(wire.as_bytes()).is_err(),
            "Rust contract requires an integer token for u64 fields"
        );
    }
}

#[test]
fn schema_bytes_and_checkout_attributes_are_lf_pinned() {
    let bytes = legitimacy::trajectory::TRAJECTORY_SCHEMA_BYTES_V0;
    assert!(bytes.ends_with(b"\n"));
    assert!(!bytes.contains(&b'\r'));

    let attributes =
        std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/.gitattributes"))
            .expect("repository attributes must be readable");
    assert!(
        attributes
            .lines()
            .any(|line| { line == "schemas/trajectory-v0.schema.json text eol=lf" })
    );
}

fn collect_numeric_maxima(value: &Value, path: &str, maxima: &mut BTreeMap<String, u64>) {
    match value {
        Value::Object(object) => {
            for (key, child) in object {
                let escaped = key.replace('~', "~0").replace('/', "~1");
                let child_path = format!("{path}/{escaped}");
                if key == "maximum" {
                    maxima.insert(
                        child_path.clone(),
                        child
                            .as_u64()
                            .expect("trajectory schema maxima must be nonnegative integers"),
                    );
                }
                collect_numeric_maxima(child, &child_path, maxima);
            }
        }
        Value::Array(values) => {
            for (index, child) in values.iter().enumerate() {
                collect_numeric_maxima(child, &format!("{path}/{index}"), maxima);
            }
        }
        _ => {}
    }
}

fn assert_interoperable_numeric_bounds(value: &Value, path: &str) {
    const MAX_INTEROPERABLE_INTEGER: u64 = 9_007_199_254_740_991;

    match value {
        Value::Object(object) => {
            for (key, child) in object {
                let child_path = format!("{path}/{key}");
                if matches!(key.as_str(), "minimum" | "maximum") {
                    let Value::Number(number) = child else {
                        panic!("numeric bound at {child_path} must be a JSON number");
                    };
                    let within_ceiling = if let Some(integer) = number.as_i64() {
                        integer.unsigned_abs() <= MAX_INTEROPERABLE_INTEGER
                    } else if let Some(integer) = number.as_u64() {
                        integer <= MAX_INTEROPERABLE_INTEGER
                    } else {
                        let float = number
                            .as_f64()
                            .expect("JSON number must convert to a finite f64");
                        assert!(float.is_finite(), "bound at {child_path} must be finite");
                        float.abs() <= MAX_INTEROPERABLE_INTEGER as f64
                    };
                    assert!(
                        within_ceiling,
                        "numeric bound at {child_path} exceeds the IEEE-754 interoperable integer ceiling"
                    );
                }
                assert_interoperable_numeric_bounds(child, &child_path);
            }
        }
        Value::Array(values) => {
            for (index, child) in values.iter().enumerate() {
                assert_interoperable_numeric_bounds(child, &format!("{path}/{index}"));
            }
        }
        _ => {}
    }
}
