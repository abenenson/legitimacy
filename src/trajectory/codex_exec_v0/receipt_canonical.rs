use super::*;

impl SyntheticFixtureReceiptV0 {
    pub(super) fn encode(&self, output: &mut Vec<u8>) {
        field_string(output, "authority", "synthetic-fixture");
        encode_common(
            output,
            &self.receipt_format,
            &self.receipt_version,
            &self.evidence_class,
        );
        encode_emitter(output, &self.emitter);
        field_u64(output, "full-jsonl-length", self.full_jsonl_length);
        field_string(output, "full-jsonl-digest", &self.full_jsonl_digest);
        field_u64(output, "raw-record-count", self.raw_record_count);
        encode_seal(output, "raw-capture-seal", &self.raw_capture_seal);
        encode_binding(output, "fixture-spec-manifest", &self.fixture_spec_manifest);
        encode_nonce(
            output,
            self.asserted_nonce_source.label(),
            &self.blinding_nonce_lower_hex,
        );
    }
}

impl ProcessCaptureReceiptV0 {
    pub(super) fn encode(&self, output: &mut Vec<u8>) {
        field_string(output, "authority", "process-capture");
        encode_common(
            output,
            &self.receipt_format,
            &self.receipt_version,
            &self.evidence_class,
        );
        encode_emitter(output, &self.emitter);
        field_string(output, "executable-sha256", &self.executable_sha256);
        encode_inode(output, "executable-inode", &self.executable_inode);
        field_string(
            output,
            "executable-execution-binding",
            &self.executable_execution_binding,
        );
        field_string(
            output,
            "artifact-open-discipline",
            &self.artifact_open_discipline,
        );
        field_string(
            output,
            "workspace-execution-discipline",
            &self.workspace_execution_discipline,
        );
        field_u64(output, "argv-count", self.argv.argument_count);
        field_u64(output, "argv-total-bytes", self.argv.total_bytes);
        field_len(
            output,
            "argv-arguments",
            self.argv.arguments_lower_hex.len(),
        );
        for argument in &self.argv.arguments_lower_hex {
            put_string(output, argument);
        }
        field_string(
            output,
            "resolved-mode",
            match self.resolved_mode {
                FreshExecModeV0::FreshExecStructuredStdin => "fresh-exec-structured-stdin",
            },
        );
        field_string(
            output,
            "capture-profile",
            match self.capture_profile {
                CaptureProfileV0::UnixReadOnlyStdinJsonV0 => "unix-read-only-stdin-json-v0",
            },
        );
        encode_input_seal(output, &self.stdin);
        encode_termination(output, &self.termination);
        encode_stream(output, "stdout", &self.stdout);
        encode_stream(output, "stderr", &self.stderr);
        field_u64(output, "raw-record-count", self.raw_record_count);
        encode_seal(output, "raw-capture-seal", &self.raw_capture_seal);
        encode_binding(output, "capture-tool", &self.capture_tool.identity);
        field_string(
            output,
            "capture-tool-file-sha256",
            &self.capture_tool.file_sha256,
        );
        encode_inode(output, "capture-tool-inode", &self.capture_tool.inode);
        encode_binding(
            output,
            "capture-profile-artifact",
            &self.capture_profile_artifact,
        );
        field_len(output, "workspace-manifest", self.workspace_manifest.len());
        for entry in &self.workspace_manifest {
            put_u64(output, entry.ordinal);
            put_string(output, &entry.role);
            put_string(output, &entry.format);
            put_string(output, &entry.relative_path_lower_hex);
            put_u64(output, entry.byte_length);
            put_string(output, &entry.sha256);
            put_u64(output, entry.inode.dev);
            put_u64(output, entry.inode.ino);
        }
        field_string(output, "workspace-tree-digest", &self.workspace_tree_digest);
        encode_release(output, "release-asset", &self.release_asset);
        encode_release(output, "sigstore-bundle", &self.sigstore_bundle);
        field_string(output, "sigstore-verification", &self.sigstore_verification);
        encode_nonce(
            output,
            self.asserted_nonce_source.label(),
            &self.blinding_nonce_lower_hex,
        );
    }
}

impl SanitizedDerivedCaptureReceiptV0 {
    pub(super) fn encode(&self, output: &mut Vec<u8>) {
        field_string(output, "authority", "sanitized-derived-capture");
        encode_common(
            output,
            &self.receipt_format,
            &self.receipt_version,
            &self.evidence_class,
        );
        field_string(
            output,
            "asserted-parent-receipt",
            self.asserted_parent_receipt.label(),
        );
        field_string(
            output,
            "asserted-origin-evidence-class",
            &self.asserted_origin_evidence_class,
        );
        field_string(
            output,
            "parent-receipt-commitment",
            &self.parent_receipt_commitment,
        );
        field_u64(
            output,
            "parent-full-jsonl-length",
            self.parent_full_jsonl_length,
        );
        field_string(
            output,
            "parent-full-jsonl-digest",
            &self.parent_full_jsonl_digest,
        );
        encode_seal(
            output,
            "parent-raw-capture-seal",
            &self.parent_raw_capture_seal,
        );
        encode_binding(output, "sanitizer-policy", &self.sanitizer_policy);
        encode_binding(output, "sanitizer-artifact", &self.sanitizer_artifact);
        field_u64(
            output,
            "derived-full-jsonl-length",
            self.derived_full_jsonl_length,
        );
        field_string(
            output,
            "derived-full-jsonl-digest",
            &self.derived_full_jsonl_digest,
        );
        encode_seal(
            output,
            "derived-raw-capture-seal",
            &self.derived_raw_capture_seal,
        );
        encode_nonce(
            output,
            self.asserted_nonce_source.label(),
            &self.blinding_nonce_lower_hex,
        );
    }
}

fn encode_common(output: &mut Vec<u8>, format: &str, version: &str, class: &str) {
    field_string(output, "receipt-format", format);
    field_string(output, "receipt-version", version);
    field_string(output, "evidence-class", class);
}

fn encode_emitter(output: &mut Vec<u8>, value: &EmitterIdentityV0) {
    field_string(output, "emitter-package-version", &value.package_version);
    field_string(output, "emitter-source-tag", &value.source_tag);
    field_string(
        output,
        "emitter-source-tag-object-sha",
        &value.source_tag_object_sha,
    );
    field_string(
        output,
        "emitter-source-commit-sha",
        &value.source_commit_sha,
    );
}

fn encode_binding(output: &mut Vec<u8>, name: &str, value: &ArtifactBindingV0) {
    put_string(output, name);
    put_string(output, &value.identity);
    put_string(output, &value.version);
    put_string(output, &value.hash);
}

fn encode_seal(output: &mut Vec<u8>, name: &str, value: &RawCaptureSealV0) {
    put_string(output, name);
    put_u64(output, value.record_count);
    put_string(output, &value.digest);
}

fn encode_inode(output: &mut Vec<u8>, name: &str, value: &InodeIdentityV0) {
    put_string(output, name);
    put_u64(output, value.dev);
    put_u64(output, value.ino);
}

fn encode_input_seal(output: &mut Vec<u8>, value: &ByteInputSealV0) {
    put_string(output, "stdin");
    match value {
        ByteInputSealV0::Absent => output.push(0),
        ByteInputSealV0::Present {
            byte_length,
            sha256,
        } => {
            output.push(1);
            put_u64(output, *byte_length);
            put_string(output, sha256);
        }
    }
}

fn encode_termination(output: &mut Vec<u8>, value: &ProcessTerminationV0) {
    put_string(output, "termination");
    match value {
        ProcessTerminationV0::Exited { code } => {
            output.push(0);
            output.push(*code);
        }
        ProcessTerminationV0::Signaled {
            signal,
            core_dumped,
        } => {
            output.push(1);
            output.push(*signal);
            output.push(u8::from(*core_dumped));
        }
    }
}

fn encode_stream(output: &mut Vec<u8>, name: &str, value: &ByteStreamSealV0) {
    put_string(output, name);
    put_u64(output, value.byte_length);
    put_string(output, &value.sha256);
}

fn encode_release(output: &mut Vec<u8>, name: &str, value: &ReleaseArtifactV0) {
    put_string(output, name);
    put_string(output, &value.name);
    put_string(output, &value.sha256);
}

fn encode_nonce(output: &mut Vec<u8>, kind: &str, nonce: &str) {
    field_string(output, "nonce-kind", kind);
    field_string(output, "blinding-nonce-lower-hex", nonce);
}

fn field_string(output: &mut Vec<u8>, name: &str, value: &str) {
    put_string(output, name);
    put_string(output, value);
}

fn field_u64(output: &mut Vec<u8>, name: &str, value: u64) {
    put_string(output, name);
    put_u64(output, value);
}

fn field_len(output: &mut Vec<u8>, name: &str, value: usize) {
    field_u64(output, name, value as u64);
}

fn put_string(output: &mut Vec<u8>, value: &str) {
    put_u64(output, value.len() as u64);
    output.extend_from_slice(value.as_bytes());
}

fn put_u64(output: &mut Vec<u8>, value: u64) {
    output.extend_from_slice(&value.to_be_bytes());
}
