//! Source locations for supported hooks and registration macros. Masking affects
//! provenance spans only; syn parsing remains the accepted-language authority.

use super::{RustHookCoreRegistration, RustHookCoreSourceSpan, registration_from_macro_tokens};

#[derive(Clone, Copy)]
struct ByteSpan {
    start: usize,
    end: usize,
}

pub(super) struct RustHookCoreSpanIndex<'source> {
    source: &'source str,
    mask: Vec<u8>,
    registration_spans: Vec<ByteSpan>,
}

impl<'source> RustHookCoreSpanIndex<'source> {
    pub(super) fn new(source: &'source str) -> Self {
        let mask = rust_source_mask(source);
        let registration_spans = collect_registration_spans(&mask);
        Self {
            source,
            mask,
            registration_spans,
        }
    }

    pub(super) fn function_span(&self, name: &str) -> Option<RustHookCoreSourceSpan> {
        let bytes = self.mask.as_slice();
        let mut cursor = 0;
        while let Some(fn_index) = find_token(bytes, cursor, b"fn") {
            let name_start = skip_ascii_whitespace(bytes, fn_index + 2);
            let name_end = name_start.checked_add(name.len())?;
            if bytes.get(name_start..name_end) == Some(name.as_bytes())
                && is_token_boundary(bytes, name_end)
            {
                let open_brace = find_byte(bytes, name_end, b'{')?;
                let close_brace = matching_delimiter(bytes, open_brace, b'{', b'}')?;
                return Some(self.source_span(fn_index, close_brace));
            }
            cursor = fn_index + 2;
        }
        None
    }

    pub(super) fn registration_span(
        &mut self,
        registration: &RustHookCoreRegistration,
    ) -> Option<RustHookCoreSourceSpan> {
        let index = self.registration_spans.iter().position(|span| {
            let snippet = &self.source[span.start..=span.end];
            syn::parse_str::<syn::ItemMacro>(snippet).is_ok_and(|item| {
                registration_from_macro_tokens(&item.mac.tokens.to_string()).is_ok_and(
                    |candidate| {
                        candidate.event == registration.event
                            && candidate.callback == registration.callback
                    },
                )
            })
        })?;
        let span = self.registration_spans.remove(index);
        Some(self.source_span(span.start, span.end))
    }

    fn source_span(&self, start: usize, end: usize) -> RustHookCoreSourceSpan {
        RustHookCoreSourceSpan {
            line_start: line_number_at(self.source, start),
            line_end: line_number_at(self.source, end),
        }
    }
}

fn collect_registration_spans(mask: &[u8]) -> Vec<ByteSpan> {
    let mut spans = Vec::new();
    let mut cursor = 0;
    while let Some(start) = find_token(mask, cursor, b"register_hook") {
        let bang = skip_ascii_whitespace(mask, start + "register_hook".len());
        if mask.get(bang) != Some(&b'!') {
            cursor = start + "register_hook".len();
            continue;
        }
        let delimiter_start = skip_ascii_whitespace(mask, bang + 1);
        let Some((open, close)) = mask.get(delimiter_start).and_then(delimiter_pair) else {
            cursor = bang + 1;
            continue;
        };
        let Some(delimiter_end) = matching_delimiter(mask, delimiter_start, open, close) else {
            cursor = delimiter_start + 1;
            continue;
        };
        let semicolon = skip_ascii_whitespace(mask, delimiter_end + 1);
        let end = if mask.get(semicolon) == Some(&b';') {
            semicolon
        } else {
            delimiter_end
        };
        spans.push(ByteSpan { start, end });
        cursor = end + 1;
    }
    spans
}

fn rust_source_mask(source: &str) -> Vec<u8> {
    let bytes = source.as_bytes();
    let mut mask = bytes.to_vec();
    let mut index = 0;
    while index < bytes.len() {
        if let Some(end) = raw_string_end(bytes, index) {
            mask_range(&mut mask, index, end);
            index = end + 1;
        } else if bytes.get(index..index + 2) == Some(b"//") {
            let end = find_line_end(bytes, index + 2);
            mask_range(&mut mask, index, end.saturating_sub(1));
            index = end;
        } else if bytes.get(index..index + 2) == Some(b"/*") {
            let end = block_comment_end(bytes, index + 2);
            mask_range(&mut mask, index, end);
            index = end + 1;
        } else if bytes[index] == b'"' {
            let end = quoted_literal_end(bytes, index, b'"');
            mask_range(&mut mask, index, end);
            index = end + 1;
        } else if bytes[index] == b'\'' && !is_lifetime_start(bytes, index) {
            let end = quoted_literal_end(bytes, index, b'\'');
            mask_range(&mut mask, index, end);
            index = end + 1;
        } else {
            index += 1;
        }
    }
    mask
}

fn mask_range(mask: &mut [u8], start: usize, end: usize) {
    let bounded_end = end.min(mask.len().saturating_sub(1));
    for byte in &mut mask[start..=bounded_end] {
        if *byte != b'\n' && *byte != b'\r' {
            *byte = b' ';
        }
    }
}

fn raw_string_end(bytes: &[u8], start: usize) -> Option<usize> {
    let mut index = start;
    if bytes.get(index) == Some(&b'b') && bytes.get(index + 1) == Some(&b'r') {
        index += 1;
    }
    if bytes.get(index) != Some(&b'r') {
        return None;
    }
    let mut hashes = 0;
    let mut quote_index = index + 1;
    while bytes.get(quote_index) == Some(&b'#') {
        hashes += 1;
        quote_index += 1;
    }
    if bytes.get(quote_index) != Some(&b'"') {
        return None;
    }
    let mut cursor = quote_index + 1;
    while cursor < bytes.len() {
        if bytes[cursor] == b'"'
            && bytes
                .get(cursor + 1..cursor + 1 + hashes)
                .is_some_and(|suffix| suffix.iter().all(|byte| *byte == b'#'))
        {
            return Some(cursor + hashes);
        }
        cursor += 1;
    }
    Some(bytes.len().saturating_sub(1))
}

fn quoted_literal_end(bytes: &[u8], start: usize, quote: u8) -> usize {
    let mut cursor = start + 1;
    while cursor < bytes.len() {
        if bytes[cursor] == b'\\' {
            cursor += 2;
        } else if bytes[cursor] == quote {
            return cursor;
        } else {
            cursor += 1;
        }
    }
    bytes.len().saturating_sub(1)
}

fn block_comment_end(bytes: &[u8], start: usize) -> usize {
    let mut depth = 1;
    let mut cursor = start;
    while cursor + 1 < bytes.len() {
        if bytes.get(cursor..cursor + 2) == Some(b"/*") {
            depth += 1;
            cursor += 2;
        } else if bytes.get(cursor..cursor + 2) == Some(b"*/") {
            depth -= 1;
            cursor += 2;
            if depth == 0 {
                return cursor - 1;
            }
        } else {
            cursor += 1;
        }
    }
    bytes.len().saturating_sub(1)
}

fn find_line_end(bytes: &[u8], start: usize) -> usize {
    bytes[start..]
        .iter()
        .position(|byte| *byte == b'\n')
        .map(|offset| start + offset)
        .unwrap_or(bytes.len())
}

fn is_lifetime_start(bytes: &[u8], index: usize) -> bool {
    bytes
        .get(index + 1)
        .is_some_and(|byte| byte.is_ascii_alphabetic() || *byte == b'_')
}

fn find_token(bytes: &[u8], mut cursor: usize, token: &[u8]) -> Option<usize> {
    while cursor + token.len() <= bytes.len() {
        let index = find_bytes(bytes, cursor, token)?;
        let end = index + token.len();
        if is_token_boundary_before(bytes, index) && is_token_boundary(bytes, end) {
            return Some(index);
        }
        cursor = end;
    }
    None
}

fn find_bytes(bytes: &[u8], start: usize, needle: &[u8]) -> Option<usize> {
    bytes[start..]
        .windows(needle.len())
        .position(|window| window == needle)
        .map(|offset| start + offset)
}

fn find_byte(bytes: &[u8], start: usize, needle: u8) -> Option<usize> {
    bytes[start..]
        .iter()
        .position(|byte| *byte == needle)
        .map(|offset| start + offset)
}

fn skip_ascii_whitespace(bytes: &[u8], mut cursor: usize) -> usize {
    while bytes
        .get(cursor)
        .is_some_and(|byte| byte.is_ascii_whitespace())
    {
        cursor += 1;
    }
    cursor
}

fn is_token_boundary_before(bytes: &[u8], index: usize) -> bool {
    index == 0 || is_token_boundary(bytes, index - 1)
}

fn is_token_boundary(bytes: &[u8], index: usize) -> bool {
    !bytes
        .get(index)
        .is_some_and(|byte| byte.is_ascii_alphanumeric() || *byte == b'_')
}

fn delimiter_pair(open: &u8) -> Option<(u8, u8)> {
    match open {
        b'(' => Some((*open, b')')),
        b'[' => Some((*open, b']')),
        b'{' => Some((*open, b'}')),
        _ => None,
    }
}

fn matching_delimiter(bytes: &[u8], open_index: usize, open: u8, close: u8) -> Option<usize> {
    let mut depth = 0;
    for (offset, byte) in bytes[open_index..].iter().enumerate() {
        if *byte == open {
            depth += 1;
        } else if *byte == close {
            depth -= 1;
            if depth == 0 {
                return Some(open_index + offset);
            }
        }
    }
    None
}

fn line_number_at(source: &str, byte_index: usize) -> usize {
    source.as_bytes()[..byte_index.min(source.len())]
        .iter()
        .filter(|byte| **byte == b'\n')
        .count()
        + 1
}
