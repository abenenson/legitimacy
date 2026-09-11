use legitimacy::trajectory::codex_exec_v0::{
    AdapterErrorCodeV0, ProcessCaptureRequestV0, capture_codex_process_v0,
};
use std::collections::BTreeMap;
use std::ffi::OsString;
use std::path::PathBuf;

const HELP: &str = "Owner-private typed Codex 0.144.0 process capture\n\nUsage: legitimacy-codex-capture-v0 [OPTIONS]\n\nOptions:\n  --native-executable <PATH>       Pinned native Codex ELF\n  --release-archive <PATH>         Pinned release tar.gz\n  --sigstore-bundle <PATH>         Pinned Sigstore bundle\n  --stdin-artifact <PATH>          Owner-only exact stdin bytes\n  --workspace <PATH>               Owner-only empty workspace\n  --capture-profile-artifact <PATH> Exact fixed capture profile bytes\n  --output-directory <PATH>        New owner-private output directory\n  -h, --help                       Print help\n";

const OPTIONS: &[&str] = &[
    "--native-executable",
    "--release-archive",
    "--sigstore-bundle",
    "--stdin-artifact",
    "--workspace",
    "--capture-profile-artifact",
    "--output-directory",
];

fn main() {
    match run(std::env::args_os().skip(1).collect()) {
        Ok(()) => {}
        Err(code) => {
            eprintln!("{}", code.as_str());
            std::process::exit(1);
        }
    }
}

fn run(arguments: Vec<OsString>) -> Result<(), AdapterErrorCodeV0> {
    if arguments.len() == 1 && matches!(arguments[0].to_str(), Some("-h" | "--help")) {
        print!("{HELP}");
        return Ok(());
    }
    let mut parsed = BTreeMap::new();
    let mut index = 0;
    while index < arguments.len() {
        let option = arguments[index]
            .to_str()
            .filter(|value| OPTIONS.contains(value))
            .ok_or(AdapterErrorCodeV0::UnsupportedInputProfile)?;
        let value = arguments
            .get(index + 1)
            .filter(|value| !value.is_empty())
            .ok_or(AdapterErrorCodeV0::UnsupportedInputProfile)?;
        if parsed.insert(option, PathBuf::from(value)).is_some() {
            return Err(AdapterErrorCodeV0::UnsupportedInputProfile);
        }
        index += 2;
    }
    if parsed.len() != OPTIONS.len() {
        return Err(AdapterErrorCodeV0::UnsupportedInputProfile);
    }
    let mut take = |name| {
        parsed
            .remove(name)
            .ok_or(AdapterErrorCodeV0::UnsupportedInputProfile)
    };
    let request = ProcessCaptureRequestV0::new(
        take("--native-executable")?,
        take("--release-archive")?,
        take("--sigstore-bundle")?,
        take("--stdin-artifact")?,
        take("--workspace")?,
        take("--capture-profile-artifact")?,
        take("--output-directory")?,
    );
    capture_codex_process_v0(&request).map_err(|failure| failure.code())
}
