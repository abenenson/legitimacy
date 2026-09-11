use super::{COMPLETED, FAILED, trusted};
use legitimacy::trajectory::codex_exec_v0::{
    AdapterErrorCodeV0, InputAuthorityReceiptV0, InspectedShareableSanitizedBundleV0,
    MAX_AUTHORITY_RECEIPT_BYTES_V0, MAX_CODEX_JSONL_BYTES_V0,
    MAX_OWNER_PRIVATE_LINEAGE_SIDECAR_BYTES_V0, MAX_TRUSTED_CONTEXT_BYTES_V0,
    OwnerPrivateLineageSidecarV0, SyntheticFixtureReceiptV0, codex_exec_fixture_spec_binding_v0,
    sanitize_capture_v0,
};

const MAGIC: &[u8] = b"legitimacy.codex-exec-v0.owner-private-lineage.v1\0";
const VERSION: u8 = 1;
const HEADER_BYTES: usize = MAGIC.len() + 1 + 5 * size_of::<u64>();

struct SidecarParts<'a> {
    child: &'a [u8],
    authority: &'a [u8],
    context: &'a [u8],
    original_parent_commitment: &'a [u8],
    reblinding_nonce: &'a [u8],
    public_parent_commitment: &'a [u8],
}

#[test]
fn owner_private_sidecar_round_trips_without_exporting_parent_provenance() {
    let parent = random_parent_for(COMPLETED);
    let original_parent_commitment = parent.commitment();
    let first = built_pair(COMPLETED, &parent);
    assert!(first.0.len() <= MAX_OWNER_PRIVATE_LINEAGE_SIDECAR_BYTES_V0);
    assert!(!contains(&first.1, original_parent_commitment.as_bytes()));
    let first_value: serde_json::Value = serde_json::from_slice(&first.1).unwrap();
    assert!(first_value.get("public_parent_commitment").is_none());
    assert!(
        first_value["public_derived_receipt"]
            .get("public_parent_commitment")
            .is_none()
    );
    assert!(
        first_value["public_transformation"]
            .get("public_parent_commitment")
            .is_none()
    );

    let sidecar = OwnerPrivateLineageSidecarV0::from_binary_slice(&first.0).unwrap();
    assert_eq!(
        format!("{sidecar:?}"),
        "OwnerPrivateLineageSidecarV0 { <redacted> }"
    );
    let inspected = InspectedShareableSanitizedBundleV0::from_json_slice(&first.1).unwrap();
    sidecar
        .revalidate_public_bundle(inspected)
        .unwrap()
        .validate()
        .unwrap();
}

#[test]
fn owner_private_sidecar_rejects_magic_version_truncation_trailing_and_caps() {
    let bytes = built_sidecar();
    let mut bad_magic = bytes.clone();
    bad_magic[0] ^= 1;
    assert_code(&bad_magic, AdapterErrorCodeV0::LineageSidecarShape);

    let mut bad_version = bytes.clone();
    bad_version[MAGIC.len()] = VERSION + 1;
    assert_code(&bad_version, AdapterErrorCodeV0::LineageSidecarShape);

    for end in [
        0,
        MAGIC.len() - 1,
        MAGIC.len(),
        HEADER_BYTES - 1,
        HEADER_BYTES,
        bytes.len() - 1,
    ] {
        assert_code(&bytes[..end], AdapterErrorCodeV0::LineageSidecarShape);
    }

    let mut trailing = bytes.clone();
    trailing.push(0);
    assert_code(&trailing, AdapterErrorCodeV0::LineageSidecarShape);

    for (slot, cap) in [
        (0, MAX_CODEX_JSONL_BYTES_V0),
        (1, MAX_AUTHORITY_RECEIPT_BYTES_V0),
        (2, MAX_TRUSTED_CONTEXT_BYTES_V0),
    ] {
        let mut one_over = bytes.clone();
        set_length(&mut one_over, slot, cap as u64 + 1);
        assert_code(&one_over, AdapterErrorCodeV0::InputTooLarge);

        let mut overflow = bytes.clone();
        set_length(&mut overflow, slot, u64::MAX);
        assert_code(&overflow, AdapterErrorCodeV0::InputTooLarge);
    }

    let total_one_over = vec![0; MAX_OWNER_PRIVATE_LINEAGE_SIDECAR_BYTES_V0 + 1];
    assert_code(&total_one_over, AdapterErrorCodeV0::InputTooLarge);
}

#[test]
fn owner_private_sidecar_requires_canonical_component_encodings() {
    let bytes = built_sidecar();
    let parts = parts(&bytes);

    let mut noncanonical_authority = vec![b' '];
    noncanonical_authority.extend_from_slice(parts.authority);
    assert_code(
        &frame(
            parts.child,
            &noncanonical_authority,
            parts.context,
            parts.original_parent_commitment,
            parts.reblinding_nonce,
            parts.public_parent_commitment,
        ),
        AdapterErrorCodeV0::LineageSidecarShape,
    );

    let mut noncanonical_context = vec![b'\n'];
    noncanonical_context.extend_from_slice(parts.context);
    assert_code(
        &frame(
            parts.child,
            parts.authority,
            &noncanonical_context,
            parts.original_parent_commitment,
            parts.reblinding_nonce,
            parts.public_parent_commitment,
        ),
        AdapterErrorCodeV0::LineageSidecarShape,
    );
}

#[test]
fn owner_private_sidecar_rejects_each_private_pair_component_mutation() {
    let bytes = built_sidecar();
    let parts = parts(&bytes);

    let mut changed_child = parts.child.to_vec();
    mutate_after(&mut changed_child, b"thread_id\":\"");
    assert_code(
        &frame(
            &changed_child,
            parts.authority,
            parts.context,
            parts.original_parent_commitment,
            parts.reblinding_nonce,
            parts.public_parent_commitment,
        ),
        AdapterErrorCodeV0::ReceiptMismatch,
    );

    let mut changed_authority = parts.authority.to_vec();
    mutate_after(&mut changed_authority, b"blinding_nonce_lower_hex\":\"");
    assert_code(
        &frame(
            parts.child,
            &changed_authority,
            parts.context,
            parts.original_parent_commitment,
            parts.reblinding_nonce,
            parts.public_parent_commitment,
        ),
        AdapterErrorCodeV0::TrustedContextMismatch,
    );

    let mut changed_context = parts.context.to_vec();
    mutate_after(
        &mut changed_context,
        b"expected_authority_commitment\":\"sha256:",
    );
    assert_code(
        &frame(
            parts.child,
            parts.authority,
            &changed_context,
            parts.original_parent_commitment,
            parts.reblinding_nonce,
            parts.public_parent_commitment,
        ),
        AdapterErrorCodeV0::TrustedContextMismatch,
    );

    let mut original_parent = parts.original_parent_commitment.to_vec();
    original_parent[7] ^= 1;
    assert_code(
        &frame(
            parts.child,
            parts.authority,
            parts.context,
            &original_parent,
            parts.reblinding_nonce,
            parts.public_parent_commitment,
        ),
        AdapterErrorCodeV0::LineageSidecarShape,
    );

    let mut nonce = parts.reblinding_nonce.to_vec();
    nonce[0] ^= 1;
    assert_code(
        &frame(
            parts.child,
            parts.authority,
            parts.context,
            parts.original_parent_commitment,
            &nonce,
            parts.public_parent_commitment,
        ),
        AdapterErrorCodeV0::LineageSidecarShape,
    );

    let mut public_parent = parts.public_parent_commitment.to_vec();
    public_parent[7] ^= 1;
    assert_code(
        &frame(
            parts.child,
            parts.authority,
            parts.context,
            parts.original_parent_commitment,
            parts.reblinding_nonce,
            &public_parent,
        ),
        AdapterErrorCodeV0::LineageSidecarShape,
    );
}

#[test]
fn owner_private_sidecar_cannot_revalidate_a_different_public_bundle() {
    let first_parent = random_parent_for(COMPLETED);
    let first = built_pair(COMPLETED, &first_parent);
    let second_parent = random_parent_for(FAILED);
    let second = built_pair(FAILED, &second_parent);
    let inspected = InspectedShareableSanitizedBundleV0::from_json_slice(&second.1).unwrap();
    let error = OwnerPrivateLineageSidecarV0::from_binary_slice(&first.0)
        .unwrap()
        .revalidate_public_bundle(inspected)
        .unwrap_err();
    assert_eq!(error.code(), AdapterErrorCodeV0::BundleMismatch);
}

#[test]
fn owner_private_sidecar_rejects_canonical_nonderived_authority() {
    let bytes = built_sidecar();
    let parts = parts(&bytes);
    let authority = random_parent_for(COMPLETED);
    let context = trusted(&authority);
    let mutant = frame(
        COMPLETED,
        &serde_json::to_vec(&authority).unwrap(),
        &serde_json::to_vec(&context).unwrap(),
        parts.original_parent_commitment,
        parts.reblinding_nonce,
        parts.public_parent_commitment,
    );
    assert_code(&mutant, AdapterErrorCodeV0::LineageSidecarShape);
}

fn random_parent_for(jsonl: &[u8]) -> InputAuthorityReceiptV0 {
    InputAuthorityReceiptV0::SyntheticFixture(
        SyntheticFixtureReceiptV0::new(jsonl, codex_exec_fixture_spec_binding_v0()).unwrap(),
    )
}

fn built_pair(jsonl: &[u8], parent: &InputAuthorityReceiptV0) -> (Vec<u8>, Vec<u8>) {
    let transaction = sanitize_capture_v0(jsonl, parent, &trusted(parent)).unwrap();
    let (sidecar, bundle) = transaction.into_publication_pair().unwrap();
    (sidecar.into_bytes(), bundle.to_json_line().unwrap())
}

fn built_sidecar() -> Vec<u8> {
    let parent = random_parent_for(COMPLETED);
    built_pair(COMPLETED, &parent).0
}

fn parts(bytes: &[u8]) -> SidecarParts<'_> {
    assert_eq!(&bytes[..MAGIC.len()], MAGIC);
    assert_eq!(bytes[MAGIC.len()], VERSION);
    let mut cursor = MAGIC.len() + 1;
    let lengths: [usize; 5] = std::array::from_fn(|_| {
        let length = u64::from_be_bytes(bytes[cursor..cursor + 8].try_into().unwrap()) as usize;
        cursor += 8;
        length
    });
    assert_eq!(cursor, HEADER_BYTES);
    let child_end = cursor + lengths[0];
    let authority_end = child_end + lengths[1];
    let context_end = authority_end + lengths[2];
    let original_parent_end = context_end + lengths[3];
    let nonce_end = original_parent_end + 32;
    let public_parent_end = nonce_end + lengths[4];
    assert_eq!(public_parent_end, bytes.len());
    SidecarParts {
        child: &bytes[cursor..child_end],
        authority: &bytes[child_end..authority_end],
        context: &bytes[authority_end..context_end],
        original_parent_commitment: &bytes[context_end..original_parent_end],
        reblinding_nonce: &bytes[original_parent_end..nonce_end],
        public_parent_commitment: &bytes[nonce_end..public_parent_end],
    }
}

fn frame(
    child: &[u8],
    authority: &[u8],
    context: &[u8],
    original_parent_commitment: &[u8],
    reblinding_nonce: &[u8],
    public_parent_commitment: &[u8],
) -> Vec<u8> {
    let mut output = Vec::new();
    output.extend_from_slice(MAGIC);
    output.push(VERSION);
    for component in [
        child,
        authority,
        context,
        original_parent_commitment,
        public_parent_commitment,
    ] {
        output.extend_from_slice(&(component.len() as u64).to_be_bytes());
    }
    output.extend_from_slice(child);
    output.extend_from_slice(authority);
    output.extend_from_slice(context);
    output.extend_from_slice(original_parent_commitment);
    output.extend_from_slice(reblinding_nonce);
    output.extend_from_slice(public_parent_commitment);
    output
}

fn set_length(bytes: &mut [u8], slot: usize, value: u64) {
    let start = MAGIC.len() + 1 + slot * size_of::<u64>();
    bytes[start..start + size_of::<u64>()].copy_from_slice(&value.to_be_bytes());
}

fn mutate_after(bytes: &mut [u8], needle: &[u8]) {
    let position = bytes
        .windows(needle.len())
        .position(|window| window == needle)
        .unwrap();
    let selected = &mut bytes[position + needle.len()];
    *selected = if *selected == b'0' { b'1' } else { b'0' };
}

fn contains(haystack: &[u8], needle: &[u8]) -> bool {
    haystack
        .windows(needle.len())
        .any(|window| window == needle)
}

fn assert_code(bytes: &[u8], expected: AdapterErrorCodeV0) {
    assert_eq!(
        OwnerPrivateLineageSidecarV0::from_binary_slice(bytes)
            .unwrap_err()
            .code(),
        expected
    );
}
