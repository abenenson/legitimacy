use super::error::{AdapterErrorCodeV0, AdapterErrorV0, AdapterResultV0};
use std::path::PathBuf;

const DEFAULT_TIMEOUT_SECONDS: u64 = 900;

/// Explicit inputs for one owner-private Codex process capture.
pub struct ProcessCaptureRequestV0 {
    native_executable: PathBuf,
    release_archive: PathBuf,
    sigstore_bundle: PathBuf,
    stdin_artifact: PathBuf,
    workspace: PathBuf,
    capture_profile_artifact: PathBuf,
    output_directory: PathBuf,
}

impl ProcessCaptureRequestV0 {
    pub fn new(
        native_executable: PathBuf,
        release_archive: PathBuf,
        sigstore_bundle: PathBuf,
        stdin_artifact: PathBuf,
        workspace: PathBuf,
        capture_profile_artifact: PathBuf,
        output_directory: PathBuf,
    ) -> Self {
        Self {
            native_executable,
            release_archive,
            sigstore_bundle,
            stdin_artifact,
            workspace,
            capture_profile_artifact,
            output_directory,
        }
    }
}

impl std::fmt::Debug for ProcessCaptureRequestV0 {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("ProcessCaptureRequestV0 { <redacted> }")
    }
}

/// Executes and publishes one fixed-profile capture.
///
/// The Linux transaction requires a single-purpose host process at entry:
/// exactly one live thread and no preexisting child.
pub fn capture_codex_process_v0(request: &ProcessCaptureRequestV0) -> AdapterResultV0<()> {
    #[cfg(target_os = "linux")]
    {
        platform::capture(request)
    }
    #[cfg(not(target_os = "linux"))]
    {
        let _ = request;
        Err(AdapterErrorV0::from_code(
            AdapterErrorCodeV0::UnsupportedPlatform,
        ))
    }
}

#[path = "process_capture_platform.rs"]
mod platform;
