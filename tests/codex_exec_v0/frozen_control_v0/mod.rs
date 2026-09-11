#![allow(dead_code)]

use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

mod frozen_manual_paths;
use frozen_manual_paths::{ADAPTER_CORE_PATHS, SANITIZER_ONLY_PATHS};

#[path = "../../fixtures/selected-authority-frozen-control-v0/source_binding_registry_inventory_support.rs"]
mod inventory_support;
use inventory_support::*;

#[path = "../../fixtures/selected-authority-frozen-control-v0/source_binding_registry_route_bindings.rs"]
mod route_bindings;
use route_bindings::*;

#[path = "../../fixtures/selected-authority-frozen-control-v0/source_binding_registry_sensitive_shapes.rs"]
mod sensitive_shapes;
use sensitive_shapes::*;

#[path = "../../fixtures/selected-authority-frozen-control-v0/source_binding_registry_syntax_support.rs"]
mod syntax_support;
use syntax_support::*;

#[path = "../../fixtures/selected-authority-frozen-control-v0/source_binding_registry_sensitive_verification.rs"]
mod sensitive_verification;
use sensitive_verification::*;

pub(super) fn adapter_core_paths() -> &'static [&'static str] {
    ADAPTER_CORE_PATHS
}

pub(super) fn sanitizer_only_paths() -> &'static [&'static str] {
    SANITIZER_ONLY_PATHS
}

pub(super) fn verify(sources: &BTreeMap<String, String>) -> Result<(), &'static str> {
    verify_registered_sensitive_type_surfaces(sources)
}

fn ordered_unique_fragments(source: &str, fragments: &[&str]) -> Result<(), &'static str> {
    let mut previous = 0;
    for fragment in fragments {
        if source.matches(fragment).count() != 1 {
            return Err("route-shape");
        }
        let offset = source.find(fragment).ok_or("route-shape")?;
        if offset < previous {
            return Err("route-shape");
        }
        previous = offset + fragment.len();
    }
    Ok(())
}
