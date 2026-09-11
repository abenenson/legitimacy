use std::ffi::OsString;
use std::fs::OpenOptions;
use std::io::Write;
use std::os::unix::fs::OpenOptionsExt;
use std::path::Path;
use std::process::{Command, ExitCode};

const SCHEMA: &[u8] = b"legitimacy.selected-authority.proxy-invocation\0";
const MAX_ARGV_ENTRIES: usize = 512;
const MAX_ARGV_BYTES: usize = 1024 * 1024;
const MAX_ENV_ENTRIES: usize = 4096;
const MAX_ENV_BYTES: usize = 4 * 1024 * 1024;
const MAX_SLOTS: u16 = 512;

fn main() -> ExitCode {
    match run() {
        Ok(code) => ExitCode::from(code),
        Err(message) => {
            eprintln!("selected compiler proxy: {message}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<u8, &'static str> {
    let mut argv = std::env::args_os();
    let _proxy = argv.next().ok_or("missing proxy argv")?;
    let compiler = utf8(argv.next().ok_or("missing compiler argv")?)?;
    let forwarded = argv
        .map(utf8)
        .collect::<Result<Vec<_>, _>>()?;
    bound_strings(&forwarded, MAX_ARGV_ENTRIES, MAX_ARGV_BYTES)?;

    let mut environment = std::env::vars_os()
        .map(|(name, value)| Ok((utf8(name)?, utf8(value)?)))
        .collect::<Result<Vec<_>, &'static str>>()?;
    environment.sort_by(|left, right| left.0.as_bytes().cmp(right.0.as_bytes()));
    if environment.windows(2).any(|pair| pair[0].0 == pair[1].0) {
        return Err("duplicate environment name");
    }
    let environment_bytes = environment.iter().try_fold(0usize, |total, (name, value)| {
        total
            .checked_add(name.len())
            .and_then(|total| total.checked_add(value.len()))
            .ok_or("environment byte overflow")
    })?;
    if environment.len() > MAX_ENV_ENTRIES || environment_bytes > MAX_ENV_BYTES {
        return Err("environment cap");
    }

    if let Some(record_root) = std::env::var_os("LEGITIMACY_SELECTED_AUTHORITY_RECORD_ROOT") {
        let record_root = Path::new(&record_root);
        claim_slot(record_root, &compiler, &forwarded, &environment)?;
    }

    let status = Command::new(&compiler)
        .args(&forwarded)
        .status()
        .map_err(|_| "compiler spawn")?;
    Ok(status
        .code()
        .and_then(|code| u8::try_from(code).ok())
        .unwrap_or(1))
}

fn claim_slot(
    root: &Path,
    compiler: &str,
    argv: &[String],
    environment: &[(String, String)],
) -> Result<(), &'static str> {
    let mut record = Vec::new();
    record.extend_from_slice(SCHEMA);
    frame(&mut record, compiler.as_bytes())?;
    record.extend_from_slice(&u32::try_from(argv.len()).map_err(|_| "argv count")?.to_be_bytes());
    for argument in argv {
        frame(&mut record, argument.as_bytes())?;
    }
    record.extend_from_slice(
        &u32::try_from(environment.len())
            .map_err(|_| "environment count")?
            .to_be_bytes(),
    );
    for (name, value) in environment {
        frame(&mut record, name.as_bytes())?;
        frame(&mut record, value.as_bytes())?;
    }
    for slot in 0..MAX_SLOTS {
        let path = root.join(format!(".slot.{slot:03}.v1"));
        let mut options = OpenOptions::new();
        options.write(true).create_new(true).mode(0o600);
        match options.open(path) {
            Ok(mut file) => {
                file.write_all(&record).map_err(|_| "slot write")?;
                file.flush().map_err(|_| "slot flush")?;
                file.sync_all().map_err(|_| "slot sync")?;
                return Ok(());
            }
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
            Err(_) => return Err("slot create"),
        }
    }
    Err("slot cap")
}

fn frame(output: &mut Vec<u8>, bytes: &[u8]) -> Result<(), &'static str> {
    output.extend_from_slice(&u64::try_from(bytes.len()).map_err(|_| "frame length")?.to_be_bytes());
    output.extend_from_slice(bytes);
    Ok(())
}

fn bound_strings(values: &[String], entries: usize, bytes: usize) -> Result<(), &'static str> {
    let total = values
        .iter()
        .try_fold(0usize, |total, value| total.checked_add(value.len()).ok_or("argv byte overflow"))?;
    if values.len() > entries || total > bytes {
        Err("argv cap")
    } else {
        Ok(())
    }
}

fn utf8(value: OsString) -> Result<String, &'static str> {
    value.into_string().map_err(|_| "non-UTF-8 process input")
}
