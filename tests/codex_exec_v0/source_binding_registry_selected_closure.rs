use super::BUILD_INPUT_PATH;
use super::module_graph::{
    ActiveModuleGraph, SelectedCfg, derive_active_library_graph, normalize_repository_path,
    visit_active_items,
};
use super::selected_artifacts::{parse_canonical_inputs, selected_cargo_artifacts};
use crate::repository_object::read_repository_file;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::sync::OnceLock;

const CAPABILITY_ERROR: &str = "capability-shape";

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum ClosureViolation {
    ArtifactMultiplicity,
    ArtifactIdentity,
    ArtifactRoot,
    DuplicateDepInfo,
    CompilerClosure,
    SelectedInputRead,
    ModuleGraph,
    SelectedInputAccounting,
    SelectedOwnerMultiplicity,
    OwnerIncomingEdge,
    OwnerBinding,
    OwnerSubtree,
    SanitizerRegistry,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CargoArtifactRecord {
    pub(super) target_name: String,
    pub(super) target_kind: String,
    pub(super) src_path: String,
    pub(super) profile_test: bool,
    pub(super) features: BTreeSet<String>,
    pub(super) filenames: Vec<String>,
    pub(super) raw_dep_info_entries: Vec<String>,
    pub(super) normalized_dep_info_entries: Vec<String>,
}

impl CargoArtifactRecord {
    pub(super) fn root(&self) -> &str {
        &self.src_path
    }

    pub(super) fn profile_test(&self) -> bool {
        self.profile_test
    }

    pub(super) fn features(&self) -> &BTreeSet<String> {
        &self.features
    }

    pub(super) fn filenames(&self) -> &[String] {
        &self.filenames
    }

    pub(super) fn raw_dep_info_entries(&self) -> &[String] {
        &self.raw_dep_info_entries
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(super) enum SelectedInputRole {
    Binary,
    LibraryModule,
    EmbeddedData,
    CanonicalObject,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SelectedInput {
    bytes: Vec<u8>,
    roles: BTreeSet<SelectedInputRole>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PortableSelectedRustClosure {
    library_artifact: CargoArtifactRecord,
    binary_artifact: CargoArtifactRecord,
    canonical_binary: BTreeSet<String>,
    canonical_library: BTreeSet<String>,
    canonical_object: String,
    actual_binary: BTreeSet<String>,
    actual_library: BTreeSet<String>,
    inputs: BTreeMap<String, SelectedInput>,
    graph: ActiveModuleGraph,
    adapter_components: Vec<String>,
    sanitizer_components: Vec<String>,
    owner_path: String,
}

impl PortableSelectedRustClosure {
    pub(super) fn library_root(&self) -> &str {
        self.library_artifact.root()
    }

    pub(super) fn binary_root(&self) -> &str {
        self.binary_artifact.root()
    }

    pub(super) fn library_artifact(&self) -> &CargoArtifactRecord {
        &self.library_artifact
    }

    pub(super) fn binary_artifact(&self) -> &CargoArtifactRecord {
        &self.binary_artifact
    }

    pub(super) fn selected_paths(&self) -> BTreeSet<String> {
        self.inputs.keys().cloned().collect()
    }

    pub(super) fn library_paths(&self) -> &BTreeSet<String> {
        &self.actual_library
    }

    pub(super) fn binary_paths(&self) -> &BTreeSet<String> {
        &self.actual_binary
    }

    pub(super) fn module_files(&self) -> &BTreeSet<String> {
        self.graph.module_files()
    }

    pub(super) fn embedded_data(&self) -> &BTreeSet<String> {
        self.graph.embedded_data()
    }

    pub(super) fn owner_path(&self) -> &str {
        &self.owner_path
    }

    pub(super) fn owner_incoming_count(&self) -> usize {
        self.graph.incoming_count(&self.owner_path)
    }

    pub(super) fn owner_parent(&self) -> &str {
        self.graph
            .module_edges()
            .iter()
            .find(|edge| edge.to == self.owner_path)
            .map(|edge| edge.from.as_str())
            .unwrap()
    }

    pub(super) fn sanitizer_components(&self) -> &[String] {
        &self.sanitizer_components
    }

    pub(super) fn adapter_components(&self) -> &[String] {
        &self.adapter_components
    }

    pub(super) fn module_edges(&self) -> BTreeSet<(String, String)> {
        self.graph
            .module_edges()
            .iter()
            .map(|edge| (edge.from.clone(), edge.to.clone()))
            .collect()
    }

    pub(super) fn semantic_module_keys(&self) -> Result<BTreeSet<String>, &'static str> {
        Ok(self.semantic_module_sources()?.into_keys().collect())
    }

    pub(super) fn binding_source_path(&self) -> &str {
        self.graph
            .module_files()
            .iter()
            .find(|path| {
                self.source(path).is_ok_and(|source| {
                    source.contains("ADAPTER_CORE_SOURCES_V0")
                        && source.contains("SANITIZER_ONLY_SOURCES_V0")
                })
            })
            .map(String::as_str)
            .unwrap()
    }

    pub(super) fn input_roles(&self, path: &str) -> Option<&BTreeSet<SelectedInputRole>> {
        self.inputs.get(path).map(|input| &input.roles)
    }

    pub(super) fn source(&self, path: &str) -> Result<&str, &'static str> {
        let input = self.inputs.get(path).ok_or(CAPABILITY_ERROR)?;
        std::str::from_utf8(&input.bytes).map_err(|_| CAPABILITY_ERROR)
    }

    pub(super) fn semantic_module_sources(&self) -> Result<BTreeMap<String, String>, &'static str> {
        let mut keys = self.graph.module_files().clone();
        keys.extend(
            self.inputs
                .iter()
                .filter(|(_, input)| input.roles.contains(&SelectedInputRole::Binary))
                .map(|(path, _)| path.clone()),
        );
        keys.iter()
            .map(|path| {
                let input = self.inputs.get(path).ok_or(CAPABILITY_ERROR)?;
                Ok((
                    path.clone(),
                    std::str::from_utf8(&input.bytes)
                        .map_err(|_| CAPABILITY_ERROR)?
                        .to_string(),
                ))
            })
            .collect()
    }

    pub(super) fn synthetic_inputs(&self) -> SyntheticSelectedRustInputs {
        SyntheticSelectedRustInputs {
            canonical_binary: self.canonical_binary.iter().cloned().collect(),
            canonical_library: self.canonical_library.iter().cloned().collect(),
            canonical_object: self.canonical_object.clone(),
            expected_library_root: self.library_artifact.src_path.clone(),
            expected_binary_root: self.binary_artifact.src_path.clone(),
            library_artifact: self.library_artifact.clone(),
            binary_artifact: self.binary_artifact.clone(),
            repository_bytes: self
                .inputs
                .iter()
                .map(|(path, input)| (path.clone(), input.bytes.clone()))
                .collect(),
        }
    }

    pub(super) fn rebuild_with_semantic_module_sources(
        &self,
        sources: &BTreeMap<String, String>,
    ) -> Result<Self, ClosureViolation> {
        let mut inputs = self.synthetic_inputs();
        let existing = self
            .semantic_module_sources()
            .map_err(|_| ClosureViolation::SelectedInputRead)?
            .into_keys()
            .collect();
        let supplied = sources.keys().cloned().collect::<BTreeSet<_>>();
        if !supplied.is_superset(&existing) {
            return Err(ClosureViolation::SelectedInputRead);
        }
        for (path, source) in sources {
            inputs
                .repository_bytes
                .insert(path.clone(), source.as_bytes().to_vec());
        }
        inputs.build()
    }
}

#[derive(Clone, Debug)]
pub(super) struct SyntheticSelectedRustInputs {
    canonical_binary: Vec<String>,
    canonical_library: Vec<String>,
    canonical_object: String,
    expected_library_root: String,
    expected_binary_root: String,
    library_artifact: CargoArtifactRecord,
    binary_artifact: CargoArtifactRecord,
    repository_bytes: BTreeMap<String, Vec<u8>>,
}

impl SyntheticSelectedRustInputs {
    pub(super) fn replace_bytes(&mut self, path: &str, mutate: impl FnOnce(&str) -> String) {
        let original = std::str::from_utf8(self.repository_bytes.get(path).unwrap()).unwrap();
        let mutation = mutate(original);
        assert_ne!(original, mutation, "{path}: mutation must differ");
        self.repository_bytes
            .insert(path.to_string(), mutation.into_bytes());
    }

    pub(super) fn insert_library_source(&mut self, path: &str, source: String) {
        assert!(
            self.repository_bytes
                .insert(path.to_string(), source.into_bytes())
                .is_none()
        );
        self.canonical_library.push(path.to_string());
        self.canonical_library.sort();
        self.library_artifact
            .raw_dep_info_entries
            .push(path.to_string());
        self.library_artifact
            .normalized_dep_info_entries
            .push(path.to_string());
    }

    pub(super) fn remove_library_source(&mut self, path: &str) {
        self.repository_bytes.remove(path);
        self.canonical_library.retain(|candidate| candidate != path);
        self.library_artifact
            .raw_dep_info_entries
            .retain(|candidate| candidate != path);
        self.library_artifact
            .normalized_dep_info_entries
            .retain(|candidate| candidate != path);
    }

    pub(super) fn duplicate_library_dep_info(&mut self, path: &str) {
        self.library_artifact
            .raw_dep_info_entries
            .push(path.to_string());
    }

    pub(super) fn set_library_artifact_root(&mut self, path: &str) {
        self.library_artifact.src_path = path.to_string();
    }

    pub(super) fn set_binary_artifact_root(&mut self, path: &str) {
        self.binary_artifact.src_path = path.to_string();
    }

    pub(super) fn set_library_features(&mut self, features: BTreeSet<String>) {
        self.library_artifact.features = features;
    }

    pub(super) fn set_library_profile_test(&mut self, profile_test: bool) {
        self.library_artifact.profile_test = profile_test;
    }

    pub(super) fn selected_library_contains(&self, path: &str) -> bool {
        self.canonical_library
            .iter()
            .any(|candidate| candidate == path)
            && self
                .library_artifact
                .normalized_dep_info_entries
                .iter()
                .any(|candidate| candidate == path)
            && self.repository_bytes.contains_key(path)
    }

    pub(super) fn active_graph(&self) -> Result<ActiveModuleGraph, ClosureViolation> {
        derive_active_library_graph(
            &self.library_artifact.src_path,
            &self.repository_bytes,
            &SelectedCfg::new(
                self.library_artifact.profile_test,
                self.library_artifact.features.clone(),
            ),
        )
        .map_err(|_| ClosureViolation::ModuleGraph)
    }

    pub(super) fn build(self) -> Result<PortableSelectedRustClosure, ClosureViolation> {
        construct_verified_closure(self)
    }
}

pub(super) fn verify_synthetic_selected_closure(
    inputs: SyntheticSelectedRustInputs,
) -> Result<(), &'static str> {
    let closure = inputs.build().map_err(|_| CAPABILITY_ERROR)?;
    super::verify_selected_sensitive_type_surfaces(&closure)
}

pub(super) fn selected_rust_closure(
    root: &Path,
) -> Result<&'static PortableSelectedRustClosure, ClosureViolation> {
    static CLOSURE: OnceLock<Result<PortableSelectedRustClosure, ClosureViolation>> =
        OnceLock::new();
    let expected = std::fs::canonicalize(env!("CARGO_MANIFEST_DIR"))
        .map_err(|_| ClosureViolation::SelectedInputRead)?;
    let supplied = std::fs::canonicalize(root).map_err(|_| ClosureViolation::SelectedInputRead)?;
    if supplied != expected {
        return Err(ClosureViolation::SelectedInputRead);
    }
    CLOSURE
        .get_or_init(|| load_selected_rust_closure(root))
        .as_ref()
        .map_err(Clone::clone)
}

pub(super) fn canonical_build_input_value() -> serde_json::Value {
    canonical_document()
        .map(|document| document.value.clone())
        .unwrap()
}

#[derive(Clone)]
struct CanonicalDocument {
    bytes: Vec<u8>,
    value: serde_json::Value,
}

fn canonical_document() -> Result<&'static CanonicalDocument, ClosureViolation> {
    static DOCUMENT: OnceLock<Result<CanonicalDocument, ClosureViolation>> = OnceLock::new();
    DOCUMENT
        .get_or_init(|| {
            let root = Path::new(env!("CARGO_MANIFEST_DIR"));
            let bytes = read_repository_file(root, BUILD_INPUT_PATH, 64 * 1024 * 1024)
                .map_err(|_| ClosureViolation::SelectedInputRead)?;
            let value =
                serde_json::from_slice(&bytes).map_err(|_| ClosureViolation::CompilerClosure)?;
            Ok(CanonicalDocument { bytes, value })
        })
        .as_ref()
        .map_err(Clone::clone)
}

fn load_selected_rust_closure(
    root: &Path,
) -> Result<PortableSelectedRustClosure, ClosureViolation> {
    let document = canonical_document()?;
    let canonical = parse_canonical_inputs(&document.value)?;
    let (library_artifact, binary_artifact) = selected_cargo_artifacts(root)?;
    let reconciled = reconcile_compiler_inputs(
        &canonical.binary,
        &canonical.library,
        &canonical.canonical_object,
        &canonical.expected_library_root,
        &canonical.expected_binary_root,
        &library_artifact,
        &binary_artifact,
    )?;
    let mut repository_bytes = BTreeMap::new();
    repository_bytes.insert(BUILD_INPUT_PATH.to_string(), document.bytes.clone());
    for path in reconciled.actual_binary.union(&reconciled.actual_library) {
        if path == BUILD_INPUT_PATH {
            continue;
        }
        let bytes = read_repository_file(root, path, 64 * 1024 * 1024)
            .map_err(|_| ClosureViolation::SelectedInputRead)?;
        if repository_bytes.insert(path.clone(), bytes).is_some() {
            return Err(ClosureViolation::CompilerClosure);
        }
    }
    let inputs = SyntheticSelectedRustInputs {
        canonical_binary: canonical.binary,
        canonical_library: canonical.library,
        canonical_object: canonical.canonical_object,
        expected_library_root: canonical.expected_library_root,
        expected_binary_root: canonical.expected_binary_root,
        library_artifact,
        binary_artifact,
        repository_bytes,
    };
    construct_verified_closure(inputs)
}

struct ReconciledCompilerInputs {
    canonical_binary: BTreeSet<String>,
    canonical_library: BTreeSet<String>,
    canonical_object: String,
    actual_binary: BTreeSet<String>,
    actual_library: BTreeSet<String>,
    library_root: String,
    binary_root: String,
}

fn reconcile_compiler_inputs(
    canonical_binary: &[String],
    canonical_library: &[String],
    canonical_object: &str,
    expected_library_root: &str,
    expected_binary_root: &str,
    library_artifact: &CargoArtifactRecord,
    binary_artifact: &CargoArtifactRecord,
) -> Result<ReconciledCompilerInputs, ClosureViolation> {
    validate_artifact_identity(library_artifact, "lib", "legitimacy")?;
    validate_artifact_identity(binary_artifact, "bin", "legitimacy")?;
    if library_artifact.profile_test || binary_artifact.profile_test {
        return Err(ClosureViolation::ArtifactIdentity);
    }
    let canonical_binary = ordered_path_set(canonical_binary)?;
    let canonical_library = ordered_path_set(canonical_library)?;
    let canonical_object = normalize_repository_path(Path::new(canonical_object))
        .map_err(|_| ClosureViolation::CompilerClosure)?;
    if canonical_binary.contains(&canonical_object) || canonical_library.contains(&canonical_object)
    {
        return Err(ClosureViolation::CompilerClosure);
    }
    let actual_binary = artifact_input_set(binary_artifact)?;
    let actual_library = artifact_input_set(library_artifact)?;
    let mut expected_library = canonical_library.clone();
    expected_library.insert(canonical_object.clone());
    if canonical_binary != actual_binary
        || expected_library != actual_library
        || !actual_binary.is_disjoint(&actual_library)
    {
        return Err(ClosureViolation::CompilerClosure);
    }
    let library_root = normalize_repository_path(Path::new(&library_artifact.src_path))
        .map_err(|_| ClosureViolation::ArtifactRoot)?;
    let binary_root = normalize_repository_path(Path::new(&binary_artifact.src_path))
        .map_err(|_| ClosureViolation::ArtifactRoot)?;
    if library_root != expected_library_root
        || binary_root != expected_binary_root
        || !canonical_library.contains(&library_root)
        || !actual_library.contains(&library_root)
        || !canonical_binary.contains(&binary_root)
        || !actual_binary.contains(&binary_root)
    {
        return Err(ClosureViolation::ArtifactRoot);
    }
    Ok(ReconciledCompilerInputs {
        canonical_binary,
        canonical_library,
        canonical_object,
        actual_binary,
        actual_library,
        library_root,
        binary_root,
    })
}

fn construct_verified_closure(
    inputs: SyntheticSelectedRustInputs,
) -> Result<PortableSelectedRustClosure, ClosureViolation> {
    let reconciled = reconcile_compiler_inputs(
        &inputs.canonical_binary,
        &inputs.canonical_library,
        &inputs.canonical_object,
        &inputs.expected_library_root,
        &inputs.expected_binary_root,
        &inputs.library_artifact,
        &inputs.binary_artifact,
    )?;
    let ReconciledCompilerInputs {
        canonical_binary,
        canonical_library,
        canonical_object,
        actual_binary,
        actual_library,
        library_root,
        binary_root,
    } = reconciled;
    let all_selected = actual_binary
        .union(&actual_library)
        .cloned()
        .collect::<BTreeSet<_>>();
    if inputs
        .repository_bytes
        .keys()
        .cloned()
        .collect::<BTreeSet<_>>()
        != all_selected
    {
        return Err(ClosureViolation::SelectedInputRead);
    }

    let graph = derive_active_library_graph(
        &library_root,
        &inputs.repository_bytes,
        &SelectedCfg::new(
            inputs.library_artifact.profile_test,
            inputs.library_artifact.features.clone(),
        ),
    )
    .map_err(|_| ClosureViolation::ModuleGraph)?;
    let mut explained = graph.module_files().clone();
    explained.extend(graph.embedded_data().iter().cloned());
    explained.insert(canonical_object.clone());
    if explained != actual_library {
        return Err(ClosureViolation::SelectedInputAccounting);
    }

    let owner_path = derive_owner(
        &graph,
        &inputs.repository_bytes,
        &SelectedCfg::new(
            inputs.library_artifact.profile_test,
            inputs.library_artifact.features.clone(),
        ),
    )?;
    if inputs
        .library_artifact
        .normalized_dep_info_entries
        .iter()
        .filter(|path| *path == &owner_path)
        .count()
        != 1
        || !graph.module_files().contains(&owner_path)
        || graph.incoming_count(&owner_path) != 1
    {
        return Err(ClosureViolation::OwnerIncomingEdge);
    }
    if !graph.owner_subtree_is_singleton(&owner_path) {
        return Err(ClosureViolation::OwnerSubtree);
    }

    let (adapter_components, sanitizer_components) =
        derive_binding_components(&graph, &inputs.repository_bytes)?;
    if sanitizer_components
        .iter()
        .filter(|path| **path == owner_path)
        .count()
        != 1
    {
        return Err(ClosureViolation::OwnerBinding);
    }

    let mut selected_inputs = BTreeMap::new();
    for (path, bytes) in inputs.repository_bytes {
        let mut roles = BTreeSet::new();
        if actual_binary.contains(&path) {
            roles.insert(SelectedInputRole::Binary);
        }
        if graph.module_files().contains(&path) {
            roles.insert(SelectedInputRole::LibraryModule);
        }
        if graph.embedded_data().contains(&path) {
            roles.insert(SelectedInputRole::EmbeddedData);
        }
        if path == canonical_object {
            roles.insert(SelectedInputRole::CanonicalObject);
        }
        selected_inputs.insert(path, SelectedInput { bytes, roles });
    }
    Ok(PortableSelectedRustClosure {
        library_artifact: CargoArtifactRecord {
            src_path: library_root,
            ..inputs.library_artifact
        },
        binary_artifact: CargoArtifactRecord {
            src_path: binary_root,
            ..inputs.binary_artifact
        },
        canonical_binary,
        canonical_library,
        canonical_object,
        actual_binary,
        actual_library,
        inputs: selected_inputs,
        graph,
        adapter_components,
        sanitizer_components,
        owner_path,
    })
}

fn derive_owner(
    graph: &ActiveModuleGraph,
    bytes: &BTreeMap<String, Vec<u8>>,
    cfg: &SelectedCfg,
) -> Result<String, ClosureViolation> {
    let mut candidates = Vec::new();
    for path in graph.module_files() {
        let source = bytes
            .get(path)
            .and_then(|bytes| std::str::from_utf8(bytes).ok())
            .ok_or(ClosureViolation::ModuleGraph)?;
        let (mint, bundle, private_bundle_storage) = cached_owner_summary(path, source, cfg)?;
        if mint == 1 && bundle == 1 && private_bundle_storage {
            candidates.push(path.clone());
        }
    }
    if candidates.len() != 1 {
        return Err(ClosureViolation::SelectedOwnerMultiplicity);
    }
    Ok(candidates.remove(0))
}

fn cached_owner_summary(
    path: &str,
    source: &str,
    cfg: &SelectedCfg,
) -> Result<(usize, usize, bool), ClosureViolation> {
    type OwnerSummary = Result<(usize, usize, bool), ClosureViolation>;
    type OwnerSummaryCache = std::sync::Mutex<BTreeMap<String, OwnerSummary>>;
    static CACHE: OnceLock<OwnerSummaryCache> = OnceLock::new();
    let mut hasher = Sha256::new();
    hasher.update(path.as_bytes());
    hasher.update([u8::from(cfg.profile_test())]);
    for feature in cfg.features() {
        hasher.update(feature.as_bytes());
        hasher.update([0]);
    }
    hasher.update(source.as_bytes());
    let key = format!("{:x}", hasher.finalize());
    let cache = CACHE.get_or_init(|| std::sync::Mutex::new(BTreeMap::new()));
    if let Some(summary) = cache.lock().unwrap().get(&key).cloned() {
        return summary;
    }
    let mut mint = 0;
    let mut bundle = 0;
    let mut private_bundle_storage = false;
    let result = visit_active_items(path, source, cfg, |item| {
        let syn::Item::Struct(item) = item else {
            return;
        };
        if item.ident == "PublicationMintV0" && matches!(item.vis, syn::Visibility::Inherited) {
            mint += 1;
        }
        if item.ident == "ShareableSanitizedBundleV0" {
            bundle += 1;
            private_bundle_storage = matches!(item.vis, syn::Visibility::Public(_))
                && item
                    .fields
                    .iter()
                    .all(|field| matches!(field.vis, syn::Visibility::Inherited));
        }
    })
    .map(|()| (mint, bundle, private_bundle_storage))
    .map_err(|_| ClosureViolation::ModuleGraph);
    cache.lock().unwrap().insert(key, result.clone());
    result
}

fn derive_binding_components(
    graph: &ActiveModuleGraph,
    bytes: &BTreeMap<String, Vec<u8>>,
) -> Result<(Vec<String>, Vec<String>), ClosureViolation> {
    let candidates = graph
        .module_files()
        .iter()
        .filter_map(|path| {
            let source = bytes
                .get(path)
                .and_then(|bytes| std::str::from_utf8(bytes).ok())?;
            if !source.contains("ADAPTER_CORE_SOURCES_V0")
                || !source.contains("SANITIZER_ONLY_SOURCES_V0")
            {
                return None;
            }
            let syntax = syn::parse_file(source).ok()?;
            let names = syntax
                .items
                .iter()
                .filter_map(|item| match item {
                    syn::Item::Const(item) => Some(item.ident.to_string()),
                    _ => None,
                })
                .collect::<BTreeSet<_>>();
            (names.contains("ADAPTER_CORE_SOURCES_V0")
                && names.contains("SANITIZER_ONLY_SOURCES_V0"))
            .then_some((path, syntax))
        })
        .collect::<Vec<_>>();
    if candidates.len() != 1 {
        return Err(ClosureViolation::SanitizerRegistry);
    }
    let (source_path, syntax) = &candidates[0];
    let adapter = parse_registry(source_path, syntax, "ADAPTER_CORE_SOURCES_V0", bytes)?;
    let sanitizer_only = parse_registry(source_path, syntax, "SANITIZER_ONLY_SOURCES_V0", bytes)?;
    let mut sanitizer = adapter.clone();
    sanitizer.extend(sanitizer_only);
    if adapter.iter().collect::<BTreeSet<_>>().len() != adapter.len()
        || sanitizer.iter().collect::<BTreeSet<_>>().len() != sanitizer.len()
    {
        return Err(ClosureViolation::SanitizerRegistry);
    }
    Ok((adapter, sanitizer))
}

fn parse_registry(
    source_path: &str,
    syntax: &syn::File,
    name: &str,
    bytes: &BTreeMap<String, Vec<u8>>,
) -> Result<Vec<String>, ClosureViolation> {
    let expression = syntax
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == name => Some(item.expr.as_ref()),
            _ => None,
        })
        .ok_or(ClosureViolation::SanitizerRegistry)?;
    let syn::Expr::Reference(reference) = expression else {
        return Err(ClosureViolation::SanitizerRegistry);
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        return Err(ClosureViolation::SanitizerRegistry);
    };
    let source_parent = Path::new(source_path)
        .parent()
        .ok_or(ClosureViolation::SanitizerRegistry)?;
    let mut components = Vec::new();
    for element in &array.elems {
        let syn::Expr::Tuple(tuple) = element else {
            return Err(ClosureViolation::SanitizerRegistry);
        };
        if tuple.elems.len() != 2 {
            return Err(ClosureViolation::SanitizerRegistry);
        }
        let syn::Expr::Lit(label) = &tuple.elems[0] else {
            return Err(ClosureViolation::SanitizerRegistry);
        };
        let syn::Lit::Str(label) = &label.lit else {
            return Err(ClosureViolation::SanitizerRegistry);
        };
        let syn::Expr::Macro(included) = &tuple.elems[1] else {
            return Err(ClosureViolation::SanitizerRegistry);
        };
        if !included.mac.path.is_ident("include_bytes") {
            return Err(ClosureViolation::SanitizerRegistry);
        }
        let literal = syn::parse2::<syn::LitStr>(included.mac.tokens.clone())
            .map_err(|_| ClosureViolation::SanitizerRegistry)?;
        let included_path = normalize_repository_path(&source_parent.join(literal.value()))
            .map_err(|_| ClosureViolation::SanitizerRegistry)?;
        if label.value() != included_path || !bytes.contains_key(&included_path) {
            return Err(ClosureViolation::SanitizerRegistry);
        }
        components.push(included_path);
    }
    Ok(components)
}

fn validate_artifact_identity(
    artifact: &CargoArtifactRecord,
    kind: &str,
    name: &str,
) -> Result<(), ClosureViolation> {
    if artifact.target_kind != kind || artifact.target_name != name || artifact.filenames.is_empty()
    {
        return Err(ClosureViolation::ArtifactIdentity);
    }
    Ok(())
}

fn ordered_path_set(paths: &[String]) -> Result<BTreeSet<String>, ClosureViolation> {
    let normalized = paths
        .iter()
        .map(|path| {
            normalize_repository_path(Path::new(path))
                .map_err(|_| ClosureViolation::CompilerClosure)
        })
        .collect::<Result<Vec<_>, _>>()?;
    if normalized.windows(2).any(|window| window[0] >= window[1]) {
        return Err(ClosureViolation::CompilerClosure);
    }
    Ok(normalized.into_iter().collect())
}

fn artifact_input_set(
    artifact: &CargoArtifactRecord,
) -> Result<BTreeSet<String>, ClosureViolation> {
    let mut raw = BTreeSet::new();
    for path in &artifact.raw_dep_info_entries {
        if !raw.insert(path.clone()) {
            return Err(ClosureViolation::DuplicateDepInfo);
        }
    }
    if artifact.raw_dep_info_entries.len() != artifact.normalized_dep_info_entries.len() {
        return Err(ClosureViolation::CompilerClosure);
    }
    Ok(artifact
        .normalized_dep_info_entries
        .iter()
        .cloned()
        .collect())
}
