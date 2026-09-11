use clap::{Parser, Subcommand};
use legitimacy::executed_composition::{self as experiment, Knowledge, MAX_BYTES};
use std::{fs::OpenOptions, io::Read, path::PathBuf, process::ExitCode};

#[derive(Parser)]
#[command(about = "Check executed composition and same-property repair offline")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}
#[derive(Subcommand)]
enum Command {
    /// Execute the instrumented synthetic host and independently check its effects.
    Demo,
    /// Check a signed capture against a separately supplied public trust policy.
    Check {
        bundle: PathBuf,
        #[arg(long)]
        trust: PathBuf,
    },
    /// Maintainer: record fresh executions using a transient signing key; retain only public key.
    Record { output: PathBuf },
}
fn bounded_read(path: &PathBuf) -> Result<Vec<u8>, String> {
    let mut bytes = vec![];
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.custom_flags(libc::O_NONBLOCK);
    }
    let file = options.open(path).map_err(|e| e.to_string())?;
    if !file.metadata().map_err(|e| e.to_string())?.is_file() {
        return Err("input must be a regular file".into());
    }
    file.take(MAX_BYTES + 1)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    if bytes.len() as u64 > MAX_BYTES {
        return Err("input exceeds 1 MiB".into());
    }
    Ok(bytes)
}
fn run(cli: Cli) -> Result<bool, String> {
    let reports = match cli.command {
        Command::Demo => experiment::suite()
            .iter()
            .map(experiment::check)
            .collect::<Vec<_>>(),
        Command::Check { bundle, trust } => {
            let signed = experiment::parse_bundle(&bounded_read(&bundle)?)?;
            let trust = bounded_read(&trust)?;
            signed
                .iter()
                .map(|s| experiment::check_signed(s, &trust))
                .collect()
        }
        Command::Record { output } => {
            experiment::record_suite(&output)?;
            return Ok(true);
        }
    };
    println!(
        "{}",
        serde_json::to_string_pretty(&reports).map_err(|e| e.to_string())?
    );
    Ok(!reports.iter().any(|r| r.knowledge == Knowledge::Invalid))
}
fn main() -> ExitCode {
    match run(Cli::parse()) {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::from(2),
        Err(e) => {
            eprintln!("invalid input: {e}");
            ExitCode::from(2)
        }
    }
}
