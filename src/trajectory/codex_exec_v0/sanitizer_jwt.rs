use serde_json::Value;

const JWT_JSON_SEGMENT_MAX_ENCODED_BYTES_V0: usize = 4 * 1024;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum JwtJsonEvidenceV0 {
    Object,
    NotObject,
    ResourceBoundExceeded,
}

pub(super) fn contains_jwt_like(surface: &[u8]) -> bool {
    surface
        .split(|byte| !byte.is_ascii_alphanumeric() && !matches!(byte, b'-' | b'_' | b'.'))
        .any(|token| {
            let mut parts = token.split(|byte| *byte == b'.');
            let (Some(header), Some(payload), Some(signature), None) =
                (parts.next(), parts.next(), parts.next(), parts.next())
            else {
                return false;
            };
            if token.len() < 12
                || ![header, payload, signature]
                    .iter()
                    .all(|part| is_feasible_base64url_segment(part))
            {
                return false;
            }
            let header_evidence = bounded_jwt_json_object(header);
            let payload_evidence = bounded_jwt_json_object(payload);
            header_evidence == JwtJsonEvidenceV0::ResourceBoundExceeded
                || payload_evidence == JwtJsonEvidenceV0::ResourceBoundExceeded
                || (header_evidence == JwtJsonEvidenceV0::Object
                    && payload_evidence == JwtJsonEvidenceV0::Object)
        })
}

fn is_feasible_base64url_segment(segment: &[u8]) -> bool {
    segment.len() >= 2
        && segment.len() % 4 != 1
        && segment
            .iter()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_'))
}

fn bounded_jwt_json_object(segment: &[u8]) -> JwtJsonEvidenceV0 {
    if segment.len() > JWT_JSON_SEGMENT_MAX_ENCODED_BYTES_V0 {
        return JwtJsonEvidenceV0::ResourceBoundExceeded;
    }
    let Some(decoded) = decode_base64url_unpadded(segment) else {
        return JwtJsonEvidenceV0::NotObject;
    };
    match serde_json::from_slice::<Value>(&decoded) {
        Ok(Value::Object(_)) => JwtJsonEvidenceV0::Object,
        _ => JwtJsonEvidenceV0::NotObject,
    }
}

fn decode_base64url_unpadded(segment: &[u8]) -> Option<Vec<u8>> {
    let mut decoded = Vec::with_capacity(segment.len().saturating_mul(3) / 4);
    let mut chunks = segment.chunks_exact(4);
    for chunk in &mut chunks {
        let first = base64url_value(chunk[0])?;
        let second = base64url_value(chunk[1])?;
        let third = base64url_value(chunk[2])?;
        let fourth = base64url_value(chunk[3])?;
        decoded.push((first << 2) | (second >> 4));
        decoded.push((second << 4) | (third >> 2));
        decoded.push((third << 6) | fourth);
    }
    match chunks.remainder() {
        [] => {}
        [first, second] => {
            let first = base64url_value(*first)?;
            let second = base64url_value(*second)?;
            if second & 0x0f != 0 {
                return None;
            }
            decoded.push((first << 2) | (second >> 4));
        }
        [first, second, third] => {
            let first = base64url_value(*first)?;
            let second = base64url_value(*second)?;
            let third = base64url_value(*third)?;
            if third & 0x03 != 0 {
                return None;
            }
            decoded.push((first << 2) | (second >> 4));
            decoded.push((second << 4) | (third >> 2));
        }
        _ => return None,
    }
    Some(decoded)
}

fn base64url_value(byte: u8) -> Option<u8> {
    match byte {
        b'A'..=b'Z' => Some(byte - b'A'),
        b'a'..=b'z' => Some(byte - b'a' + 26),
        b'0'..=b'9' => Some(byte - b'0' + 52),
        b'-' => Some(62),
        b'_' => Some(63),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn jwt_recognition_requires_bounded_decoded_object_evidence() {
        for rejected in [
            b"e30.e30.c2lnbmF0dXJl".as_slice(),
            b"prefix:e30.e30.c2lnbmF0dXJl,suffix".as_slice(),
            b"eyJhbGciOiJIUzI1NiJ9.eyJzdWIiOiIxMjM0NTY3ODkwIn0.signature0".as_slice(),
        ] {
            assert!(contains_jwt_like(rejected), "{rejected:?}");
        }
        for accepted in [
            b"release-2026.08.30".as_slice(),
            b"v1.20.30-beta".as_slice(),
            b"W10.e30.c2lnbmF0dXJl".as_slice(),
            b"E30.e30.c2lnbmF0dXJl".as_slice(),
            b"e31.e30.c2lnbmF0dXJl".as_slice(),
            b"xe30.e30.c2lnbmF0dXJl".as_slice(),
            b"e30=.e30.c2lnbmF0dXJl".as_slice(),
            b"e30AA.e30.c2lnbmF0dXJl".as_slice(),
            b"e30.e30.c2lnbmF0dXJl.extra".as_slice(),
            b"e30.e.e30".as_slice(),
        ] {
            assert!(!contains_jwt_like(accepted), "{accepted:?}");
        }

        let oversized = "A".repeat(JWT_JSON_SEGMENT_MAX_ENCODED_BYTES_V0 + 2);
        assert_eq!(oversized.len() % 4, 2);
        assert!(contains_jwt_like(
            format!("{oversized}.e30.c2lnbmF0dXJl").as_bytes()
        ));
        assert_eq!(
            bounded_jwt_json_object(b"e31"),
            JwtJsonEvidenceV0::NotObject,
            "noncanonical trailing bits are malformed base64url"
        );
    }
}
