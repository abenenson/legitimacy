use sha2::{Digest, Sha256};
use std::collections::BTreeSet;

const MAGIC: &[u8] = b"legitimacy.selected-compiler-evidence\0";
const ENVELOPE_DOMAIN: &[u8] = b"legitimacy.selected-compiler-evidence.v1";

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub(crate) enum InvocationRole {
    Library = 0,
    Binary = 1,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub(crate) enum InputRole {
    LibraryModule = 0,
    BinaryModule = 1,
    EmbeddedData = 2,
    CanonicalObject = 3,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DigestEvidence {
    pub(crate) byte_len: u64,
    pub(crate) digest: [u8; 32],
}

impl DigestEvidence {
    pub(crate) fn from_bytes(domain: &'static [u8], bytes: &[u8]) -> Self {
        let mut hasher = Sha256::new();
        hasher.update(domain);
        hasher.update((bytes.len() as u64).to_be_bytes());
        hasher.update(bytes);
        Self {
            byte_len: bytes.len() as u64,
            digest: hasher.finalize().into(),
        }
    }

    fn encode(&self, encoder: &mut Encoder) {
        encoder.u64(self.byte_len);
        encoder.fixed(&self.digest);
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct FileIdentity {
    pub(crate) canonical_path: String,
    pub(crate) device: u64,
    pub(crate) inode: u64,
    pub(crate) byte_len: u64,
    pub(crate) digest: [u8; 32],
}

impl FileIdentity {
    fn encode(&self, encoder: &mut Encoder) -> Result<(), EnvelopeFailure> {
        encoder.absolute_path(&self.canonical_path)?;
        encoder.u64(self.device);
        encoder.u64(self.inode);
        encoder.u64(self.byte_len);
        encoder.fixed(&self.digest);
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ToolIdentity {
    pub(crate) source: DigestEvidence,
    pub(crate) executable: FileIdentity,
    pub(crate) schema_identity: String,
    pub(crate) schema_version: u16,
}

impl ToolIdentity {
    fn encode(&self, encoder: &mut Encoder) -> Result<(), EnvelopeFailure> {
        self.source.encode(encoder);
        self.executable.encode(encoder)?;
        encoder.string(&self.schema_identity);
        encoder.u16(self.schema_version);
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CargoRunEvidence {
    pub(crate) command: Vec<String>,
    pub(crate) environment: DigestEvidence,
    pub(crate) status: u32,
    pub(crate) stdout: DigestEvidence,
    pub(crate) stderr: DigestEvidence,
    pub(crate) metadata_bytes: Vec<u8>,
}

impl CargoRunEvidence {
    fn encode(&self, encoder: &mut Encoder) -> Result<(), EnvelopeFailure> {
        encoder.strings(&self.command)?;
        self.environment.encode(encoder);
        encoder.u32(self.status);
        self.stdout.encode(encoder);
        self.stderr.encode(encoder);
        encoder.bytes(&self.metadata_bytes);
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct BuildScriptEvidence {
    pub(crate) raw_record: Vec<u8>,
    pub(crate) package_id: String,
    pub(crate) out_dir: String,
    pub(crate) cfgs: Vec<String>,
    pub(crate) environment: Vec<(String, String)>,
    pub(crate) linked_libs: Vec<String>,
    pub(crate) linked_paths: Vec<String>,
    pub(crate) outputs: Vec<(String, DigestEvidence)>,
}

impl BuildScriptEvidence {
    fn encode(&self, encoder: &mut Encoder) -> Result<(), EnvelopeFailure> {
        encoder.bytes(&self.raw_record);
        encoder.string(&self.package_id);
        encoder.absolute_path(&self.out_dir)?;
        encoder.sorted_strings(&self.cfgs)?;
        encoder.sorted_string_map(&self.environment)?;
        encoder.sorted_strings(&self.linked_libs)?;
        encoder.sorted_strings(&self.linked_paths)?;
        encoder.u32(count(self.outputs.len())?);
        let mut prior = None;
        for (path, digest) in &self.outputs {
            encoder.repository_path(path)?;
            if prior
                .as_ref()
                .is_some_and(|prior: &&str| *prior >= path.as_str())
            {
                return Err(EnvelopeFailure::NonCanonicalOrder);
            }
            prior = Some(path.as_str());
            digest.encode(encoder);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ReplayEvidence {
    pub(crate) status: u32,
    pub(crate) stdout: Vec<u8>,
    pub(crate) stderr: DigestEvidence,
    pub(crate) parsed_commitment: DigestEvidence,
}

impl ReplayEvidence {
    fn encode(&self, encoder: &mut Encoder) {
        encoder.u32(self.status);
        encoder.bytes(&self.stdout);
        self.stderr.encode(encoder);
        self.parsed_commitment.encode(encoder);
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ExpansionEvidence {
    pub(crate) status: u32,
    pub(crate) stdout: DigestEvidence,
    pub(crate) stderr: DigestEvidence,
    pub(crate) node_count: u64,
    pub(crate) maximum_depth: u32,
    pub(crate) topology: DigestEvidence,
    pub(crate) authority_surface: DigestEvidence,
}

impl ExpansionEvidence {
    fn encode(&self, encoder: &mut Encoder) {
        encoder.u32(self.status);
        self.stdout.encode(encoder);
        self.stderr.encode(encoder);
        encoder.u64(self.node_count);
        encoder.u32(self.maximum_depth);
        self.topology.encode(encoder);
        self.authority_surface.encode(encoder);
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct OutputIdentity {
    pub(crate) role: u8,
    pub(crate) file: FileIdentity,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct InvocationEvidence {
    pub(crate) role: InvocationRole,
    pub(crate) package_id: String,
    pub(crate) manifest: String,
    pub(crate) root: String,
    pub(crate) forwarded_argv: Vec<String>,
    pub(crate) environment_entry_count: u32,
    pub(crate) environment: DigestEvidence,
    pub(crate) rustc_vv: Vec<u8>,
    pub(crate) target_triple: String,
    pub(crate) original_status: u32,
    pub(crate) original_stdout: DigestEvidence,
    pub(crate) original_stderr: DigestEvidence,
    pub(crate) cfg: ReplayEvidence,
    pub(crate) check_cfg: ReplayEvidence,
    pub(crate) expansion: ExpansionEvidence,
    pub(crate) dep_info: Vec<u8>,
    pub(crate) dep_info_entries: Vec<(Vec<u8>, String)>,
    pub(crate) raw_artifact_record: Vec<u8>,
    pub(crate) parsed_artifact: DigestEvidence,
    pub(crate) outputs: Vec<OutputIdentity>,
}

impl InvocationEvidence {
    fn encode(&self, encoder: &mut Encoder) -> Result<(), EnvelopeFailure> {
        encoder.u8(self.role as u8);
        encoder.string(&self.package_id);
        encoder.absolute_path(&self.manifest)?;
        encoder.repository_path(&self.root)?;
        encoder.strings(&self.forwarded_argv)?;
        encoder.u32(self.environment_entry_count);
        self.environment.encode(encoder);
        encoder.bytes(&self.rustc_vv);
        encoder.string(&self.target_triple);
        encoder.u32(self.original_status);
        self.original_stdout.encode(encoder);
        self.original_stderr.encode(encoder);
        self.cfg.encode(encoder);
        self.check_cfg.encode(encoder);
        self.expansion.encode(encoder);
        encoder.bytes(&self.dep_info);
        encoder.u32(count(self.dep_info_entries.len())?);
        for (raw, normalized) in &self.dep_info_entries {
            encoder.bytes(raw);
            encoder.repository_path(normalized)?;
        }
        encoder.bytes(&self.raw_artifact_record);
        self.parsed_artifact.encode(encoder);
        encoder.u32(count(self.outputs.len())?);
        for output in &self.outputs {
            encoder.u8(output.role);
            output.file.encode(encoder)?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ByteRoleEntry {
    pub(crate) path: String,
    pub(crate) roles: BTreeSet<InputRole>,
    pub(crate) bytes: DigestEvidence,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ProbeEvidence {
    pub(crate) exact_rlib_before: FileIdentity,
    pub(crate) command: Vec<String>,
    pub(crate) environment: DigestEvidence,
    pub(crate) status: u32,
    pub(crate) stdout: Vec<u8>,
    pub(crate) stderr: DigestEvidence,
    pub(crate) exact_rlib_after: FileIdentity,
    pub(crate) transcript: DigestEvidence,
}

impl ProbeEvidence {
    fn encode(&self, encoder: &mut Encoder) -> Result<(), EnvelopeFailure> {
        self.exact_rlib_before.encode(encoder)?;
        encoder.strings(&self.command)?;
        self.environment.encode(encoder);
        encoder.u32(self.status);
        encoder.bytes(&self.stdout);
        self.stderr.encode(encoder);
        self.exact_rlib_after.encode(encoder)?;
        self.transcript.encode(encoder);
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CompilerEvidenceFields {
    pub(crate) release_case_id: String,
    pub(crate) run_id: [u8; 16],
    pub(crate) wrapper_shape: String,
    pub(crate) rustc_vv: Vec<u8>,
    pub(crate) cargo_vv: Vec<u8>,
    pub(crate) compatibility_entry: u16,
    pub(crate) proxy: ToolIdentity,
    pub(crate) git_answer: ToolIdentity,
    pub(crate) cargo: CargoRunEvidence,
    pub(crate) build_script: BuildScriptEvidence,
    pub(crate) library: InvocationEvidence,
    pub(crate) binary: InvocationEvidence,
    pub(crate) byte_role_table: Vec<ByteRoleEntry>,
    pub(crate) probe: ProbeEvidence,
    pub(crate) closure_summary: DigestEvidence,
    pub(crate) typed_result: u8,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CompilerEvidenceEnvelopeV1 {
    bytes: Vec<u8>,
    digest: [u8; 32],
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum EnvelopeFailure {
    InvalidPath,
    NonCanonicalOrder,
    LengthOverflow,
    RoleMultiplicity,
}

impl CompilerEvidenceEnvelopeV1 {
    pub(crate) fn seal(fields: &CompilerEvidenceFields) -> Result<Self, EnvelopeFailure> {
        if fields.library.role != InvocationRole::Library
            || fields.binary.role != InvocationRole::Binary
        {
            return Err(EnvelopeFailure::RoleMultiplicity);
        }
        let mut encoder = Encoder::default();
        encoder.fixed(MAGIC);
        encoder.u16(1);
        encoder.string(&fields.release_case_id);
        encoder.fixed(&fields.run_id);
        encoder.string(&fields.wrapper_shape);
        encoder.bytes(&fields.rustc_vv);
        encoder.bytes(&fields.cargo_vv);
        encoder.u16(fields.compatibility_entry);
        fields.proxy.encode(&mut encoder)?;
        fields.git_answer.encode(&mut encoder)?;
        fields.cargo.encode(&mut encoder)?;
        fields.build_script.encode(&mut encoder)?;
        fields.library.encode(&mut encoder)?;
        fields.binary.encode(&mut encoder)?;
        encode_byte_role_table(&mut encoder, &fields.byte_role_table)?;
        fields.probe.encode(&mut encoder)?;
        fields.closure_summary.encode(&mut encoder);
        encoder.u8(fields.typed_result);
        let bytes = encoder.finish();
        let mut hasher = Sha256::new();
        hasher.update(ENVELOPE_DOMAIN);
        hasher.update((bytes.len() as u64).to_be_bytes());
        hasher.update(&bytes);
        Ok(Self {
            digest: hasher.finalize().into(),
            bytes,
        })
    }

    pub(crate) fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    pub(crate) fn digest(&self) -> [u8; 32] {
        self.digest
    }
}

fn encode_byte_role_table(
    encoder: &mut Encoder,
    entries: &[ByteRoleEntry],
) -> Result<(), EnvelopeFailure> {
    encoder.u32(count(entries.len())?);
    let mut prior = None;
    for entry in entries {
        encoder.repository_path(&entry.path)?;
        if prior
            .as_ref()
            .is_some_and(|prior: &&str| *prior >= entry.path.as_str())
        {
            return Err(EnvelopeFailure::NonCanonicalOrder);
        }
        prior = Some(entry.path.as_str());
        if entry.roles.is_empty() {
            return Err(EnvelopeFailure::RoleMultiplicity);
        }
        encoder.u32(count(entry.roles.len())?);
        for role in &entry.roles {
            encoder.u8(*role as u8);
        }
        entry.bytes.encode(encoder);
    }
    Ok(())
}

#[derive(Default)]
struct Encoder {
    bytes: Vec<u8>,
}

impl Encoder {
    fn finish(self) -> Vec<u8> {
        self.bytes
    }

    fn fixed(&mut self, value: &[u8]) {
        self.bytes.extend_from_slice(value);
    }

    fn u8(&mut self, value: u8) {
        self.bytes.push(value);
    }

    fn u16(&mut self, value: u16) {
        self.bytes.extend_from_slice(&value.to_be_bytes());
    }

    fn u32(&mut self, value: u32) {
        self.bytes.extend_from_slice(&value.to_be_bytes());
    }

    fn u64(&mut self, value: u64) {
        self.bytes.extend_from_slice(&value.to_be_bytes());
    }

    fn bytes(&mut self, value: &[u8]) {
        self.u64(value.len() as u64);
        self.fixed(value);
    }

    fn string(&mut self, value: &str) {
        self.bytes(value.as_bytes());
    }

    fn strings(&mut self, values: &[String]) -> Result<(), EnvelopeFailure> {
        self.u32(count(values.len())?);
        for value in values {
            self.string(value);
        }
        Ok(())
    }

    fn sorted_strings(&mut self, values: &[String]) -> Result<(), EnvelopeFailure> {
        if values
            .windows(2)
            .any(|pair| pair[0].as_bytes() >= pair[1].as_bytes())
        {
            return Err(EnvelopeFailure::NonCanonicalOrder);
        }
        self.strings(values)
    }

    fn sorted_string_map(&mut self, values: &[(String, String)]) -> Result<(), EnvelopeFailure> {
        if values
            .windows(2)
            .any(|pair| pair[0].0.as_bytes() >= pair[1].0.as_bytes())
        {
            return Err(EnvelopeFailure::NonCanonicalOrder);
        }
        self.u32(count(values.len())?);
        for (key, value) in values {
            self.string(key);
            self.string(value);
        }
        Ok(())
    }

    fn repository_path(&mut self, value: &str) -> Result<(), EnvelopeFailure> {
        if !is_repository_path(value) {
            return Err(EnvelopeFailure::InvalidPath);
        }
        self.string(value);
        Ok(())
    }

    fn absolute_path(&mut self, value: &str) -> Result<(), EnvelopeFailure> {
        if !value.starts_with('/') || value.contains('\0') || value.contains('\\') {
            return Err(EnvelopeFailure::InvalidPath);
        }
        let tail = &value[1..];
        if tail.is_empty()
            || tail
                .split('/')
                .any(|component| component.is_empty() || component == "." || component == "..")
        {
            return Err(EnvelopeFailure::InvalidPath);
        }
        self.string(value);
        Ok(())
    }
}

fn is_repository_path(value: &str) -> bool {
    !value.is_empty()
        && !value.starts_with('/')
        && !value.contains('\0')
        && !value.contains('\\')
        && value
            .split('/')
            .all(|component| !component.is_empty() && component != "." && component != "..")
}

fn count(value: usize) -> Result<u32, EnvelopeFailure> {
    u32::try_from(value).map_err(|_| EnvelopeFailure::LengthOverflow)
}

pub(crate) fn assert_canonical_envelope_is_strict() {
    let digest = |domain: &'static [u8], bytes: &[u8]| DigestEvidence::from_bytes(domain, bytes);
    let file = |path: &str, byte: u8| FileIdentity {
        canonical_path: path.to_string(),
        device: 7,
        inode: u64::from(byte),
        byte_len: 1,
        digest: [byte; 32],
    };
    let replay = |domain: &'static [u8]| ReplayEvidence {
        status: 0,
        stdout: b"evidence\n".to_vec(),
        stderr: digest(b"legitimacy.stderr.v1", b""),
        parsed_commitment: digest(domain, b"evidence\n"),
    };
    let invocation = |role| InvocationEvidence {
        role,
        package_id: "path+file:///case#legitimacy@1.0.0".to_string(),
        manifest: "/case/Cargo.toml".to_string(),
        root: match role {
            InvocationRole::Library => "src/lib.rs",
            InvocationRole::Binary => "cli/main.rs",
        }
        .to_string(),
        forwarded_argv: vec!["rustc".to_string(), "--crate-name".to_string()],
        environment_entry_count: 1,
        environment: digest(b"legitimacy.environment.v1", b"A=B"),
        rustc_vv: b"compiler\n".to_vec(),
        target_triple: "x86_64-unknown-linux-gnu".to_string(),
        original_status: 0,
        original_stdout: digest(b"legitimacy.original.stdout.v1", b""),
        original_stderr: digest(b"legitimacy.original.stderr.v1", b""),
        cfg: replay(b"legitimacy.cfg.atoms.v1"),
        check_cfg: replay(b"legitimacy.cfg.grammar.v1"),
        expansion: ExpansionEvidence {
            status: 0,
            stdout: digest(b"legitimacy.expanded.stdout.v1", b"expanded"),
            stderr: digest(b"legitimacy.expanded.stderr.v1", b""),
            node_count: 3,
            maximum_depth: 2,
            topology: digest(b"legitimacy.expanded.topology.v1", b"tree"),
            authority_surface: digest(b"legitimacy.expanded.authority.v1", b"surface"),
        },
        dep_info: b"target: src/lib.rs\n".to_vec(),
        dep_info_entries: vec![(b"src/lib.rs".to_vec(), "src/lib.rs".to_string())],
        raw_artifact_record: b"{\"reason\":\"compiler-artifact\"}\n".to_vec(),
        parsed_artifact: digest(b"legitimacy.cargo.artifact.v1", b"artifact"),
        outputs: vec![OutputIdentity {
            role: 0,
            file: file(
                match role {
                    InvocationRole::Library => "/target/liblegitimacy.rlib",
                    InvocationRole::Binary => "/target/legitimacy",
                },
                match role {
                    InvocationRole::Library => 1,
                    InvocationRole::Binary => 2,
                },
            ),
        }],
    };
    let fields = CompilerEvidenceFields {
        release_case_id: "clean".to_string(),
        run_id: [9; 16],
        wrapper_shape: "cargo-workspace-wrapper-argv1-real-rustc-v1".to_string(),
        rustc_vv: b"compiler\n".to_vec(),
        cargo_vv: b"cargo\n".to_vec(),
        compatibility_entry: 0,
        proxy: ToolIdentity {
            source: digest(b"legitimacy.proxy.source.v1", b"source"),
            executable: file("/tools/proxy", 3),
            schema_identity: "proxy-record".to_string(),
            schema_version: 1,
        },
        git_answer: ToolIdentity {
            source: digest(b"legitimacy.git-answer.source.v1", b"source"),
            executable: file("/tools/git-answer", 4),
            schema_identity: "git-answer-record".to_string(),
            schema_version: 1,
        },
        cargo: CargoRunEvidence {
            command: vec!["cargo".to_string(), "build".to_string()],
            environment: digest(b"legitimacy.cargo.environment.v1", b"A=B"),
            status: 0,
            stdout: digest(b"legitimacy.cargo.stdout.v1", b"json\n"),
            stderr: digest(b"legitimacy.cargo.stderr.v1", b""),
            metadata_bytes: b"{\"version\":1}".to_vec(),
        },
        build_script: BuildScriptEvidence {
            raw_record: b"{\"reason\":\"build-script-executed\"}\n".to_vec(),
            package_id: "path+file:///case#legitimacy@1.0.0".to_string(),
            out_dir: "/target/build/out".to_string(),
            cfgs: vec![],
            environment: vec![],
            linked_libs: vec![],
            linked_paths: vec![],
            outputs: vec![(
                "generated/revision.txt".to_string(),
                digest(b"legitimacy.build-output.v1", b"revision"),
            )],
        },
        library: invocation(InvocationRole::Library),
        binary: invocation(InvocationRole::Binary),
        byte_role_table: vec![
            ByteRoleEntry {
                path: "cli/main.rs".to_string(),
                roles: BTreeSet::from([InputRole::BinaryModule]),
                bytes: digest(b"legitimacy.selected-input.v1", b"bin"),
            },
            ByteRoleEntry {
                path: "contracts/canonical.json".to_string(),
                roles: BTreeSet::from([InputRole::CanonicalObject]),
                bytes: digest(b"legitimacy.selected-input.v1", b"object"),
            },
            ByteRoleEntry {
                path: "src/lib.rs".to_string(),
                roles: BTreeSet::from([InputRole::LibraryModule]),
                bytes: digest(b"legitimacy.selected-input.v1", b"lib"),
            },
            ByteRoleEntry {
                path: "src/revision.txt".to_string(),
                roles: BTreeSet::from([InputRole::EmbeddedData]),
                bytes: digest(b"legitimacy.selected-input.v1", b"data"),
            },
        ],
        probe: ProbeEvidence {
            exact_rlib_before: file("/target/liblegitimacy.rlib", 1),
            command: vec!["rustc".to_string(), "--extern".to_string()],
            environment: digest(b"legitimacy.probe.environment.v1", b"A=B"),
            status: 0,
            stdout: b"binding\n".to_vec(),
            stderr: digest(b"legitimacy.probe.stderr.v1", b""),
            exact_rlib_after: file("/target/liblegitimacy.rlib", 1),
            transcript: digest(b"legitimacy.binding.transcript.v1", b"binding"),
        },
        closure_summary: digest(b"legitimacy.closure.summary.v1", b"closed"),
        typed_result: 0,
    };
    let first = CompilerEvidenceEnvelopeV1::seal(&fields).unwrap();
    let second = CompilerEvidenceEnvelopeV1::seal(&fields).unwrap();
    assert_eq!(first.bytes(), second.bytes());
    assert_eq!(first.digest(), second.digest());
    assert!(first.bytes().starts_with(MAGIC));

    let mut unsorted = fields.clone();
    unsorted.byte_role_table.swap(0, 1);
    assert_eq!(
        CompilerEvidenceEnvelopeV1::seal(&unsorted),
        Err(EnvelopeFailure::NonCanonicalOrder)
    );
    let mut wrong_roles = fields;
    wrong_roles.library.role = InvocationRole::Binary;
    assert_eq!(
        CompilerEvidenceEnvelopeV1::seal(&wrong_roles),
        Err(EnvelopeFailure::RoleMultiplicity)
    );
}
