use std::process::Command;

const HELP: &str = "Owner-private typed Codex 0.144.0 process capture\n\nUsage: legitimacy-codex-capture-v0 [OPTIONS]\n\nOptions:\n  --native-executable <PATH>       Pinned native Codex ELF\n  --release-archive <PATH>         Pinned release tar.gz\n  --sigstore-bundle <PATH>         Pinned Sigstore bundle\n  --stdin-artifact <PATH>          Owner-only exact stdin bytes\n  --workspace <PATH>               Owner-only empty workspace\n  --capture-profile-artifact <PATH> Exact fixed capture profile bytes\n  --output-directory <PATH>        New owner-private output directory\n  -h, --help                       Print help\n";

fn binary() -> &'static str {
    env!("CARGO_BIN_EXE_legitimacy-codex-capture-v0")
}

#[test]
fn help_and_closed_argument_failures_are_exact() {
    for help in ["--help", "-h"] {
        let output = Command::new(binary()).arg(help).output().unwrap();
        assert!(output.status.success());
        assert_eq!(output.stdout, HELP.as_bytes());
        assert!(output.stderr.is_empty());
    }

    for arguments in [
        vec![],
        vec!["--unknown", "private-value"],
        vec!["--native-executable"],
        vec![
            "--native-executable",
            "/private/one",
            "--native-executable",
            "/private/two",
        ],
        vec!["--help", "private-value"],
    ] {
        let output = Command::new(binary()).args(arguments).output().unwrap();
        assert_eq!(output.status.code(), Some(1));
        assert!(output.stdout.is_empty());
        assert_eq!(output.stderr, b"unsupported-input-profile\n");
    }
}
