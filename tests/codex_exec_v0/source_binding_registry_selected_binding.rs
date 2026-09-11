use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::marker::PhantomData;
use std::path::{Component, Path};

const PROBE_MAGIC: &[u8] = b"legitimacy.selected-authority.rlib-probe\0";
const ATTESTATION_IDENTITY: &str = "legitimacy.codex-exec-v0.sanitizer-compiled-attestation";
const HASH_ENVELOPE_V0: &[u8] = b"legitimacy.trajectory.hash.v0\0";
const SANITIZER_FRAMING_DOMAIN: &str =
    "legitimacy.codex-exec-v0.sanitizer-registered-source-manifest.v0";
const SANITIZER_AGGREGATE_IDENTITY: &str = "legitimacy.codex-exec-v0.sanitizer";
const SANITIZER_AGGREGATE_VERSION: &str = "0";
const MAX_COMPONENTS: usize = 64;
const MAX_SELECTED_INPUTS: usize = 512;
const MAX_SELECTED_BYTES: usize = 128 * 1024 * 1024;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum SelectedRole {
    LibraryModule,
    BinaryModule,
    EmbeddedData,
    CanonicalObject,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SelectedByteEntry {
    bytes: Box<[u8]>,
    roles: BTreeSet<SelectedRole>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SelectedByteRoleTable {
    entries: BTreeMap<String, SelectedByteEntry>,
    digest: [u8; 32],
}

impl SelectedByteRoleTable {
    pub(crate) fn new(
        entries: BTreeMap<String, (Vec<u8>, BTreeSet<SelectedRole>)>,
    ) -> Result<Self, BindingFailure> {
        if entries.is_empty() || entries.len() > MAX_SELECTED_INPUTS {
            return Err(BindingFailure::SelectedInputAccounting);
        }
        let mut total = 0usize;
        let mut normalized = BTreeMap::new();
        for (path, (bytes, roles)) in entries {
            if normalize_path(Path::new(&path))? != path || roles.is_empty() {
                return Err(BindingFailure::SelectedInputAccounting);
            }
            total = total
                .checked_add(bytes.len())
                .ok_or(BindingFailure::SelectedInputAccounting)?;
            if bytes.len() > 64 * 1024 * 1024 || total > MAX_SELECTED_BYTES {
                return Err(BindingFailure::SelectedInputAccounting);
            }
            normalized.insert(
                path,
                SelectedByteEntry {
                    bytes: bytes.into_boxed_slice(),
                    roles,
                },
            );
        }
        let digest = table_digest(&normalized);
        Ok(Self {
            entries: normalized,
            digest,
        })
    }

    pub(crate) fn bytes(&self, path: &str) -> Result<&[u8], BindingFailure> {
        self.entries
            .get(path)
            .map(|entry| entry.bytes.as_ref())
            .ok_or(BindingFailure::SelectedInputRead)
    }

    pub(crate) fn roles(&self, path: &str) -> Result<&BTreeSet<SelectedRole>, BindingFailure> {
        self.entries
            .get(path)
            .map(|entry| &entry.roles)
            .ok_or(BindingFailure::SelectedInputRead)
    }

    pub(crate) fn keys(&self) -> impl Iterator<Item = &str> {
        self.entries.keys().map(String::as_str)
    }

    pub(crate) fn digest(&self) -> [u8; 32] {
        self.digest
    }

    fn refresh_bytes(&mut self, path: &str, bytes: Vec<u8>) -> Result<(), BindingFailure> {
        let entry = self
            .entries
            .get_mut(path)
            .ok_or(BindingFailure::SelectedInputRead)?;
        if entry.bytes.as_ref() == bytes {
            return Err(BindingFailure::CompiledTranscript);
        }
        entry.bytes = bytes.into_boxed_slice();
        self.reseal()
    }

    fn insert_component_path(
        &mut self,
        path: String,
        bytes: Vec<u8>,
        roles: BTreeSet<SelectedRole>,
    ) -> Result<(), BindingFailure> {
        if roles.is_empty()
            || normalize_path(Path::new(&path))? != path
            || self
                .entries
                .insert(
                    path,
                    SelectedByteEntry {
                        bytes: bytes.into_boxed_slice(),
                        roles,
                    },
                )
                .is_some()
        {
            return Err(BindingFailure::SelectedInputAccounting);
        }
        self.reseal()
    }

    fn reseal(&mut self) -> Result<(), BindingFailure> {
        let total = self
            .entries
            .values()
            .try_fold(0usize, |total, entry| total.checked_add(entry.bytes.len()));
        if self.entries.len() > MAX_SELECTED_INPUTS
            || total.is_none_or(|total| total > MAX_SELECTED_BYTES)
        {
            return Err(BindingFailure::SelectedInputAccounting);
        }
        self.digest = table_digest(&self.entries);
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CompiledComponentObservation {
    pub(crate) index: u32,
    pub(crate) path: String,
    pub(crate) byte_length: u64,
    pub(crate) digest: [u8; 32],
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct RlibIdentity {
    pub(crate) canonical_path: String,
    pub(crate) device: u64,
    pub(crate) inode: u64,
    pub(crate) byte_length: u64,
    pub(crate) digest: [u8; 32],
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CompiledBindingTranscript {
    pub(crate) schema_identity: String,
    pub(crate) schema_version: u16,
    pub(crate) components: Vec<CompiledComponentObservation>,
    pub(crate) aggregate_identity: String,
    pub(crate) aggregate_version: String,
    pub(crate) aggregate_hash: String,
    pub(crate) rlib: RlibIdentity,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum BindingEdit {
    RefreshBytes {
        index: u32,
        path: String,
        old_digest: [u8; 32],
        new_digest: [u8; 32],
    },
    ReplaceComponent {
        index: u32,
        old_path: String,
        old_digest: [u8; 32],
        new_path: String,
        new_digest: [u8; 32],
    },
    InsertComponent {
        index: u32,
        path: String,
        digest: [u8; 32],
    },
    RemoveComponent {
        index: u32,
        path: String,
        digest: [u8; 32],
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum BindingFailure {
    SelectedInputRead,
    SelectedInputAccounting,
    SanitizerRegistryShape,
    RlibProbe,
    CompiledTranscript,
    StaleCompilerEvidence,
    EvidenceEnvelope,
    SanitizerBindingMismatch,
}

#[derive(Clone, Debug)]
pub(crate) struct Bound {
    compiled: CompiledBindingTranscript,
    envelope_digest: [u8; 32],
    table_digest: [u8; 32],
}

#[derive(Clone, Debug)]
pub(crate) struct Unbound {
    prior: CompiledBindingTranscript,
    transformed: Vec<CompiledComponentObservation>,
    edits: Vec<BindingEdit>,
}

#[derive(Clone, Debug)]
pub(crate) struct SyntheticSelectedTree<State> {
    table: SelectedByteRoleTable,
    state: State,
    marker: PhantomData<fn() -> State>,
}

impl SyntheticSelectedTree<Bound> {
    pub(crate) fn refresh_component_bytes(
        mut self,
        index: u32,
        path: &str,
        new_bytes: Vec<u8>,
    ) -> Result<SyntheticSelectedTree<Unbound>, BindingFailure> {
        let old_digest = exact_component(&self.state.compiled.components, index, path)?.digest;
        let new_digest = Sha256::digest(&new_bytes).into();
        if new_digest == old_digest {
            return Err(BindingFailure::CompiledTranscript);
        }
        self.table.refresh_bytes(path, new_bytes)?;
        let mut transformed = self.state.compiled.components.clone();
        transformed[index as usize].digest = new_digest;
        transformed[index as usize].byte_length = u64::try_from(self.table.bytes(path)?.len())
            .map_err(|_| BindingFailure::CompiledTranscript)?;
        Ok(SyntheticSelectedTree {
            table: self.table,
            state: Unbound {
                prior: self.state.compiled,
                transformed,
                edits: vec![BindingEdit::RefreshBytes {
                    index,
                    path: path.to_string(),
                    old_digest,
                    new_digest,
                }],
            },
            marker: PhantomData,
        })
    }

    pub(crate) fn compiled(&self) -> &CompiledBindingTranscript {
        &self.state.compiled
    }

    pub(crate) fn envelope_digest(&self) -> [u8; 32] {
        self.state.envelope_digest
    }

    pub(crate) fn table(&self) -> &SelectedByteRoleTable {
        &self.table
    }
}

impl SyntheticSelectedTree<Unbound> {
    pub(crate) fn refresh_component_bytes(
        mut self,
        index: u32,
        path: &str,
        new_bytes: Vec<u8>,
    ) -> Result<Self, BindingFailure> {
        let old_digest = exact_component(&self.state.transformed, index, path)?.digest;
        let new_digest = Sha256::digest(&new_bytes).into();
        if new_digest == old_digest {
            return Err(BindingFailure::CompiledTranscript);
        }
        self.table.refresh_bytes(path, new_bytes)?;
        self.state.transformed[index as usize].digest = new_digest;
        self.state.transformed[index as usize].byte_length =
            u64::try_from(self.table.bytes(path)?.len())
                .map_err(|_| BindingFailure::CompiledTranscript)?;
        self.state.edits.push(BindingEdit::RefreshBytes {
            index,
            path: path.to_string(),
            old_digest,
            new_digest,
        });
        Ok(self)
    }

    pub(crate) fn replace_component(
        mut self,
        index: u32,
        old_path: &str,
        new_path: String,
        new_bytes: Vec<u8>,
        roles: BTreeSet<SelectedRole>,
    ) -> Result<Self, BindingFailure> {
        let old_digest = exact_component(&self.state.transformed, index, old_path)?.digest;
        let new_digest = Sha256::digest(&new_bytes).into();
        self.table
            .insert_component_path(new_path.clone(), new_bytes, roles)?;
        self.state.transformed[index as usize] = CompiledComponentObservation {
            index,
            path: new_path.clone(),
            byte_length: u64::try_from(self.table.bytes(&new_path)?.len())
                .map_err(|_| BindingFailure::CompiledTranscript)?,
            digest: new_digest,
        };
        self.state.edits.push(BindingEdit::ReplaceComponent {
            index,
            old_path: old_path.to_string(),
            old_digest,
            new_path,
            new_digest,
        });
        Ok(self)
    }

    pub(crate) fn insert_component(
        mut self,
        index: u32,
        path: String,
        bytes: Vec<u8>,
        roles: BTreeSet<SelectedRole>,
    ) -> Result<Self, BindingFailure> {
        let index_usize = usize::try_from(index).map_err(|_| BindingFailure::CompiledTranscript)?;
        if index_usize > self.state.transformed.len() {
            return Err(BindingFailure::CompiledTranscript);
        }
        let digest = Sha256::digest(&bytes).into();
        self.table
            .insert_component_path(path.clone(), bytes, roles)?;
        self.state.transformed.insert(
            index_usize,
            CompiledComponentObservation {
                index,
                path: path.clone(),
                byte_length: u64::try_from(self.table.bytes(&path)?.len())
                    .map_err(|_| BindingFailure::CompiledTranscript)?,
                digest,
            },
        );
        reindex(&mut self.state.transformed)?;
        self.state.edits.push(BindingEdit::InsertComponent {
            index,
            path,
            digest,
        });
        Ok(self)
    }

    pub(crate) fn remove_component(
        mut self,
        index: u32,
        path: &str,
    ) -> Result<Self, BindingFailure> {
        let old_digest = exact_component(&self.state.transformed, index, path)?.digest;
        self.state.transformed.remove(index as usize);
        reindex(&mut self.state.transformed)?;
        self.state.edits.push(BindingEdit::RemoveComponent {
            index,
            path: path.to_string(),
            digest: old_digest,
        });
        Ok(self)
    }

    pub(crate) fn bind_after_complete_compile_and_probe(
        self,
        compiled: CompiledBindingTranscript,
        envelope_digest: [u8; 32],
        envelope_table_digest: [u8; 32],
    ) -> Result<SyntheticSelectedTree<Bound>, BindingFailure> {
        if self.table.digest() != envelope_table_digest {
            return Err(BindingFailure::EvidenceEnvelope);
        }
        if self.state.edits.is_empty() && self.state.prior != compiled {
            return Err(BindingFailure::CompiledTranscript);
        }
        if self.state.transformed != compiled.components {
            return Err(BindingFailure::CompiledTranscript);
        }
        validate_compiled_transcript(&compiled, &self.table)?;
        Ok(SyntheticSelectedTree {
            table: self.table,
            state: Bound {
                compiled,
                envelope_digest,
                table_digest: envelope_table_digest,
            },
            marker: PhantomData,
        })
    }

    pub(crate) fn edits(&self) -> &[BindingEdit] {
        &self.state.edits
    }
}

pub(crate) fn parse_probe_record(
    bytes: &[u8],
) -> Result<CompiledBindingTranscript, BindingFailure> {
    if bytes.len() > 4 * 1024 * 1024 || !bytes.starts_with(PROBE_MAGIC) {
        return Err(BindingFailure::RlibProbe);
    }
    let mut cursor = Cursor::new(&bytes[PROBE_MAGIC.len()..]);
    if cursor.u16()? != 1 {
        return Err(BindingFailure::RlibProbe);
    }
    let schema_identity = cursor.string()?;
    let schema_version = cursor.u16()?;
    if schema_identity != ATTESTATION_IDENTITY || schema_version != 0 {
        return Err(BindingFailure::RlibProbe);
    }
    let count = cursor.u32()? as usize;
    if count == 0 || count > MAX_COMPONENTS {
        return Err(BindingFailure::RlibProbe);
    }
    let mut components = Vec::with_capacity(count);
    let mut paths = BTreeSet::new();
    for expected_index in 0..count {
        let index = cursor.u32()?;
        let path = cursor.string()?;
        let byte_length = cursor.u64()?;
        let digest = cursor.fixed32()?;
        if index as usize != expected_index
            || normalize_path(Path::new(&path))? != path
            || !paths.insert(path.clone())
        {
            return Err(BindingFailure::RlibProbe);
        }
        components.push(CompiledComponentObservation {
            index,
            path,
            byte_length,
            digest,
        });
    }
    let transcript = CompiledBindingTranscript {
        schema_identity,
        schema_version,
        components,
        aggregate_identity: cursor.string()?,
        aggregate_version: cursor.string()?,
        aggregate_hash: cursor.string()?,
        rlib: RlibIdentity {
            canonical_path: cursor.string()?,
            device: cursor.u64()?,
            inode: cursor.u64()?,
            byte_length: cursor.u64()?,
            digest: cursor.fixed32()?,
        },
    };
    if !cursor.is_empty() || !transcript.rlib.canonical_path.starts_with('/') {
        return Err(BindingFailure::RlibProbe);
    }
    Ok(transcript)
}

pub(crate) fn registry_transcript(
    binding_source_path: &str,
    table: &SelectedByteRoleTable,
) -> Result<Vec<CompiledComponentObservation>, BindingFailure> {
    let source = std::str::from_utf8(table.bytes(binding_source_path)?)
        .map_err(|_| BindingFailure::SanitizerRegistryShape)?;
    let syntax = syn::parse_file(source).map_err(|_| BindingFailure::SanitizerRegistryShape)?;
    let mut components = parse_registry(
        binding_source_path,
        &syntax,
        "ADAPTER_CORE_SOURCES_V0",
        table,
    )?;
    components.extend(parse_registry(
        binding_source_path,
        &syntax,
        "SANITIZER_ONLY_SOURCES_V0",
        table,
    )?);
    if components.is_empty()
        || components.len() > MAX_COMPONENTS
        || components
            .iter()
            .map(|component| &component.path)
            .collect::<BTreeSet<_>>()
            .len()
            != components.len()
    {
        return Err(BindingFailure::SanitizerRegistryShape);
    }
    reindex(&mut components)?;
    Ok(components)
}

pub(crate) fn validate_compiled_transcript(
    compiled: &CompiledBindingTranscript,
    table: &SelectedByteRoleTable,
) -> Result<(), BindingFailure> {
    if compiled.schema_identity != ATTESTATION_IDENTITY
        || compiled.schema_version != 0
        || compiled.components.len() > MAX_COMPONENTS
        || compiled.aggregate_identity != SANITIZER_AGGREGATE_IDENTITY
        || compiled.aggregate_version != SANITIZER_AGGREGATE_VERSION
    {
        return Err(BindingFailure::CompiledTranscript);
    }
    for component in &compiled.components {
        let bytes = table.bytes(&component.path)?;
        if component.byte_length != bytes.len() as u64
            || component.digest != <[u8; 32]>::from(Sha256::digest(bytes))
        {
            return Err(BindingFailure::SanitizerBindingMismatch);
        }
    }
    let expected_hash = aggregate_hash(&compiled.components, table)?;
    if compiled.aggregate_hash != expected_hash {
        return Err(BindingFailure::SanitizerBindingMismatch);
    }
    Ok(())
}

fn preserve_stale_compiled_sanitizer_binding_for_rejection_witness(
    table: &SelectedByteRoleTable,
    stale: &CompiledBindingTranscript,
) -> BindingFailure {
    assert_eq!(
        validate_compiled_transcript(stale, table),
        Err(BindingFailure::SanitizerBindingMismatch)
    );
    BindingFailure::SanitizerBindingMismatch
}

fn parse_registry(
    source_path: &str,
    syntax: &syn::File,
    name: &str,
    table: &SelectedByteRoleTable,
) -> Result<Vec<CompiledComponentObservation>, BindingFailure> {
    let matches = syntax
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Const(item) if item.ident == name => Some(item.expr.as_ref()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let [syn::Expr::Reference(reference)] = matches.as_slice() else {
        return Err(BindingFailure::SanitizerRegistryShape);
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        return Err(BindingFailure::SanitizerRegistryShape);
    };
    let parent = Path::new(source_path)
        .parent()
        .ok_or(BindingFailure::SanitizerRegistryShape)?;
    let mut components = Vec::new();
    for element in &array.elems {
        let syn::Expr::Tuple(tuple) = element else {
            return Err(BindingFailure::SanitizerRegistryShape);
        };
        let [syn::Expr::Lit(label), syn::Expr::Macro(included)] =
            tuple.elems.iter().collect::<Vec<_>>().as_slice()
        else {
            return Err(BindingFailure::SanitizerRegistryShape);
        };
        let syn::Lit::Str(label) = &label.lit else {
            return Err(BindingFailure::SanitizerRegistryShape);
        };
        if !included.mac.path.is_ident("include_bytes") {
            return Err(BindingFailure::SanitizerRegistryShape);
        }
        let literal = syn::parse2::<syn::LitStr>(included.mac.tokens.clone())
            .map_err(|_| BindingFailure::SanitizerRegistryShape)?;
        let path = normalize_path(&parent.join(literal.value()))?;
        if label.value() != path {
            return Err(BindingFailure::SanitizerRegistryShape);
        }
        let bytes = table.bytes(&path)?;
        components.push(CompiledComponentObservation {
            index: 0,
            path,
            byte_length: bytes.len() as u64,
            digest: Sha256::digest(bytes).into(),
        });
    }
    Ok(components)
}

fn aggregate_hash(
    components: &[CompiledComponentObservation],
    table: &SelectedByteRoleTable,
) -> Result<String, BindingFailure> {
    let mut hasher = Sha256::new();
    hasher.update(HASH_ENVELOPE_V0);
    frame_hash(&mut hasher, SANITIZER_FRAMING_DOMAIN.as_bytes());
    let count = components
        .len()
        .checked_mul(2)
        .ok_or(BindingFailure::SanitizerBindingMismatch)?;
    hasher.update((count as u64).to_be_bytes());
    for component in components {
        frame_hash(&mut hasher, component.path.as_bytes());
        frame_hash(&mut hasher, table.bytes(&component.path)?);
    }
    Ok(format!("sha256:{:x}", hasher.finalize()))
}

fn exact_component<'a>(
    components: &'a [CompiledComponentObservation],
    index: u32,
    path: &str,
) -> Result<&'a CompiledComponentObservation, BindingFailure> {
    let index_usize = usize::try_from(index).map_err(|_| BindingFailure::CompiledTranscript)?;
    let component = components
        .get(index_usize)
        .ok_or(BindingFailure::CompiledTranscript)?;
    if component.index != index || component.path != path {
        return Err(BindingFailure::CompiledTranscript);
    }
    Ok(component)
}

fn reindex(components: &mut [CompiledComponentObservation]) -> Result<(), BindingFailure> {
    for (index, component) in components.iter_mut().enumerate() {
        component.index = u32::try_from(index).map_err(|_| BindingFailure::CompiledTranscript)?;
    }
    Ok(())
}

fn table_digest(entries: &BTreeMap<String, SelectedByteEntry>) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"legitimacy.selected-byte-role-table.v1");
    hasher.update((entries.len() as u32).to_be_bytes());
    for (path, entry) in entries {
        frame_hash(&mut hasher, path.as_bytes());
        hasher.update((entry.roles.len() as u32).to_be_bytes());
        for role in &entry.roles {
            hasher.update([*role as u8]);
        }
        frame_hash(&mut hasher, &entry.bytes);
    }
    hasher.finalize().into()
}

fn frame_hash(hasher: &mut Sha256, bytes: &[u8]) {
    hasher.update((bytes.len() as u64).to_be_bytes());
    hasher.update(bytes);
}

fn normalize_path(path: &Path) -> Result<String, BindingFailure> {
    let mut components = Vec::new();
    for component in path.components() {
        match component {
            Component::Normal(value) => {
                let value = value
                    .to_str()
                    .ok_or(BindingFailure::SelectedInputAccounting)?;
                if value.is_empty() || value.contains('\\') || value.contains('\0') {
                    return Err(BindingFailure::SelectedInputAccounting);
                }
                components.push(value.to_string());
            }
            Component::CurDir => {}
            Component::ParentDir => {
                if components.pop().is_none() {
                    return Err(BindingFailure::SelectedInputAccounting);
                }
            }
            Component::RootDir | Component::Prefix(_) => {
                return Err(BindingFailure::SelectedInputAccounting);
            }
        }
    }
    let normalized = components.join("/");
    if normalized.is_empty() || normalized.len() > 4_096 {
        Err(BindingFailure::SelectedInputAccounting)
    } else {
        Ok(normalized)
    }
}

struct Cursor<'a> {
    remaining: &'a [u8],
}

impl<'a> Cursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { remaining: bytes }
    }

    fn take(&mut self, count: usize) -> Result<&'a [u8], BindingFailure> {
        if self.remaining.len() < count {
            return Err(BindingFailure::RlibProbe);
        }
        let (value, remaining) = self.remaining.split_at(count);
        self.remaining = remaining;
        Ok(value)
    }

    fn u16(&mut self) -> Result<u16, BindingFailure> {
        Ok(u16::from_be_bytes(
            self.take(2)?
                .try_into()
                .map_err(|_| BindingFailure::RlibProbe)?,
        ))
    }

    fn u32(&mut self) -> Result<u32, BindingFailure> {
        Ok(u32::from_be_bytes(
            self.take(4)?
                .try_into()
                .map_err(|_| BindingFailure::RlibProbe)?,
        ))
    }

    fn u64(&mut self) -> Result<u64, BindingFailure> {
        Ok(u64::from_be_bytes(
            self.take(8)?
                .try_into()
                .map_err(|_| BindingFailure::RlibProbe)?,
        ))
    }

    fn fixed32(&mut self) -> Result<[u8; 32], BindingFailure> {
        self.take(32)?
            .try_into()
            .map_err(|_| BindingFailure::RlibProbe)
    }

    fn string(&mut self) -> Result<String, BindingFailure> {
        let count = usize::try_from(self.u64()?).map_err(|_| BindingFailure::RlibProbe)?;
        if count > 4 * 1024 * 1024 {
            return Err(BindingFailure::RlibProbe);
        }
        std::str::from_utf8(self.take(count)?)
            .map(str::to_string)
            .map_err(|_| BindingFailure::RlibProbe)
    }

    fn is_empty(&self) -> bool {
        self.remaining.is_empty()
    }
}

#[path = "source_binding_registry_selected_final_closure.rs"]
mod final_closure;
#[path = "source_binding_registry_selected_binding_tests.rs"]
mod policy_tests;

pub(crate) fn assert_stale_compiled_binding_policy_only_fails_at_binding_comparison() {
    policy_tests::assert_stale_compiled_binding_policy_only_fails_at_binding_comparison();
}

pub(crate) fn assert_unbound_synthetic_tree_has_no_final_constructor() {
    policy_tests::assert_unbound_synthetic_tree_has_no_final_constructor();
}
