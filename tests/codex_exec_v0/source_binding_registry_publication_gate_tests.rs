use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use uuid::Uuid;

struct PublicationPolishFixture {
    root: PathBuf,
}

impl PublicationPolishFixture {
    fn create() -> Self {
        let root = std::env::temp_dir().join(format!(
            "legitimacy-publication-polish-kill-{}-{}",
            std::process::id(),
            Uuid::new_v4()
        ));
        fs::create_dir(&root).unwrap();
        fs::set_permissions(&root, fs::Permissions::from_mode(0o700)).unwrap();
        Self { root }
    }

    fn path(&self) -> &Path {
        &self.root
    }
}

impl Drop for PublicationPolishFixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

pub(crate) fn assert_ignored_maintainer_payload_cannot_mask_tracked_failure() {
    let source_root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let fixture = PublicationPolishFixture::create();
    let root = fixture.path();
    fs::create_dir(root.join("scripts")).unwrap();
    fs::create_dir(root.join("papers")).unwrap();
    fs::copy(
        source_root.join("scripts/check-publication-polish.sh"),
        root.join("scripts/check-publication-polish.sh"),
    )
    .unwrap();
    fs::write(root.join(".gitignore"), b"scripts/maintainer-denylist.sh\n").unwrap();
    fs::write(root.join("AGENTS.md"), b"seeded tracked failure\n").unwrap();
    fs::write(root.join("CONTRIBUTING.md"), b"tracked public fixture\n").unwrap();
    let init = Command::new("git")
        .args(["init", "--quiet"])
        .current_dir(root)
        .status()
        .unwrap();
    assert!(init.success());
    let add = Command::new("git")
        .args([
            "add",
            ".gitignore",
            "AGENTS.md",
            "CONTRIBUTING.md",
            "scripts/check-publication-polish.sh",
        ])
        .current_dir(root)
        .status()
        .unwrap();
    assert!(add.success());
    fs::write(
        root.join("scripts/maintainer-denylist.sh"),
        b"#!/usr/bin/env bash\nexit 0\n",
    )
    .unwrap();
    let ignored = Command::new("git")
        .args(["check-ignore", "--quiet", "scripts/maintainer-denylist.sh"])
        .current_dir(root)
        .status()
        .unwrap();
    assert!(ignored.success());
    let output = Command::new("bash")
        .arg(root.join("scripts/check-publication-polish.sh"))
        .current_dir(root)
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    assert!(
        String::from_utf8(output.stderr)
            .unwrap()
            .contains("tracked AGENTS.md must be absent from public artifacts")
    );
}
