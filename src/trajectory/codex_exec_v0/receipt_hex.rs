use super::{AdapterErrorCodeV0, AdapterErrorV0, AdapterResultV0};
use sha2::{Digest, Sha256};

pub(super) fn lower_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len().saturating_mul(2));
    for byte in bytes {
        output.push(HEX[usize::from(byte >> 4)] as char);
        output.push(HEX[usize::from(byte & 0x0f)] as char);
    }
    output
}

pub(crate) fn decode_lower_hex(value: &str) -> AdapterResultV0<Vec<u8>> {
    if !value.len().is_multiple_of(2) {
        return Err(AdapterErrorV0::new(AdapterErrorCodeV0::ReceiptShape));
    }
    value
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| {
            let high = hex_nibble(pair[0])?;
            let low = hex_nibble(pair[1])?;
            Ok((high << 4) | low)
        })
        .collect()
}

fn hex_nibble(byte: u8) -> AdapterResultV0<u8> {
    match byte {
        b'0'..=b'9' => Ok(byte - b'0'),
        b'a'..=b'f' => Ok(byte - b'a' + 10),
        _ => Err(AdapterErrorV0::new(AdapterErrorCodeV0::ReceiptShape)),
    }
}

pub(super) fn standard_sha256(bytes: &[u8]) -> String {
    format!("sha256:{:x}", Sha256::digest(bytes))
}
