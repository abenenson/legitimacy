use super::*;
use legitimacy::trajectory::codex_exec_v0::{
    MAX_OWNER_PRIVATE_LINEAGE_SIDECAR_BYTES_V0, sanitize_capture_v0,
};

#[test]
fn imported_nonce_relabel_stays_private_and_local_publication_requires_fresh_entropy() {
    let synthetic = synthetic_authority(COMPLETED);
    let synthetic_context = trusted(&synthetic);
    let mut relabeled_synthetic = serde_json::to_value(&synthetic).unwrap();
    relabeled_synthetic["asserted_nonce_source"] = serde_json::json!("capture-random");
    let relabeled_synthetic = InputAuthorityReceiptV0::from_json_slice(
        &serde_json::to_vec(&relabeled_synthetic).unwrap(),
    )
    .unwrap();
    assert_eq!(
        adapt_codex_exec_v0(COMPLETED, &relabeled_synthetic, &synthetic_context)
            .unwrap_err()
            .code(),
        AdapterErrorCodeV0::TrustedContextMismatch
    );
    let relabeled_context = trusted(&relabeled_synthetic);
    assert!(adapt_codex_exec_v0(COMPLETED, &relabeled_synthetic, &relabeled_context).is_ok());
    let original_parent_commitment = relabeled_synthetic.commitment();
    let (sidecar, bundle) =
        sanitize_capture_v0(COMPLETED, &relabeled_synthetic, &relabeled_context)
            .unwrap()
            .into_publication_pair()
            .unwrap();
    let public_bytes = bundle.to_json_line().unwrap();
    let public: serde_json::Value = serde_json::from_slice(&public_bytes).unwrap();
    assert!(
        public["public_derived_receipt"]
            .get("asserted_parent_receipt")
            .is_none()
    );
    assert!(
        public["public_derived_receipt"]
            .get("asserted_origin_evidence_class")
            .is_none()
    );
    assert!(
        !String::from_utf8(public_bytes)
            .unwrap()
            .contains(&original_parent_commitment)
    );
    assert!(sidecar.into_bytes().len() <= MAX_OWNER_PRIVATE_LINEAGE_SIDECAR_BYTES_V0);
}
