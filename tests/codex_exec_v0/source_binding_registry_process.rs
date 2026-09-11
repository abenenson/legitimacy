use std::collections::BTreeMap;
use std::fs::{self, File};
use std::io::{Read, Seek, SeekFrom};
use std::os::fd::{AsRawFd, OwnedFd};
use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use rustix::fs::{Mode, OFlags};
use rustix::io::dup;
use sha2::{Digest, Sha256};

const SUPERVISOR_SOURCE: &[u8] =
    include_bytes!("../../scripts/selected-authority-process-supervisor.py");
const STATUS_MAGIC: &str = "legitimacy.selected-authority-process.v2";
const STATUS_BYTE_CAP: usize = 4 * 1024;
const TERM_GRACE: Duration = Duration::from_secs(2);
static NEXT_SCRATCH: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ProcessResult {
    Success,
    NonzeroExit,
    Timeout,
    StdoutCap,
    StderrCap,
    LiveDescendant,
    SupervisorSignal,
    SpawnFailure,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ProcessFailure {
    SupervisorIdentity,
    Scratch,
    Spawn,
    Protocol,
    Cleanup,
}

#[derive(Debug)]
pub(crate) struct ProcessOutcome {
    pub(crate) result: ProcessResult,
    pub(crate) output: Output,
    pub(crate) term_sent: bool,
    pub(crate) kill_sent: bool,
    pub(crate) stdout_total: usize,
    pub(crate) stderr_total: usize,
    pub(crate) stdout_eof: bool,
    pub(crate) stderr_eof: bool,
    pub(crate) reaped_descendants: usize,
    pub(crate) observed_descendants: usize,
    pub(crate) group_absent: bool,
    pub(crate) descendants_absent: bool,
}

pub(crate) struct ProcessSupervisor {
    python: PinnedFile,
    source: PinnedFile,
    scratch_parent: PathBuf,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Identity {
    device: u64,
    inode: u64,
    length: u64,
    digest: [u8; 32],
}

struct PinnedFile {
    path: PathBuf,
    file: File,
    identity: Identity,
    executable: bool,
}

impl ProcessSupervisor {
    pub(crate) fn new(
        python: PathBuf,
        source: PathBuf,
        scratch_parent: PathBuf,
    ) -> Result<Self, ProcessFailure> {
        let python = PinnedFile::open(&python, true)?;
        let source = PinnedFile::open(&source, false)?;
        if source.read_bytes()? != SUPERVISOR_SOURCE {
            return Err(ProcessFailure::SupervisorIdentity);
        }
        let parent_metadata = fs::metadata(&scratch_parent).map_err(|_| ProcessFailure::Scratch)?;
        if !parent_metadata.is_dir()
            || parent_metadata.uid() != rustix::process::geteuid().as_raw()
            || parent_metadata.permissions().mode() & 0o777 != 0o700
        {
            return Err(ProcessFailure::SupervisorIdentity);
        }
        Ok(Self {
            python,
            source,
            scratch_parent,
        })
    }

    pub(crate) fn run(
        &self,
        command: &Command,
        timeout: Duration,
        stdout_cap: usize,
        stderr_cap: usize,
    ) -> Result<ProcessOutcome, ProcessFailure> {
        self.python.verify()?;
        self.source.verify()?;
        let mut scratch = ScratchDirectory::create(&self.scratch_parent)?;
        let result = self.run_inner(&mut scratch, command, timeout, stdout_cap, stderr_cap);
        let cleanup = scratch.finish();
        if cleanup.is_err() {
            return Err(ProcessFailure::Cleanup);
        }
        result
    }

    fn run_inner(
        &self,
        scratch: &mut ScratchDirectory,
        command: &Command,
        timeout: Duration,
        stdout_cap: usize,
        stderr_cap: usize,
    ) -> Result<ProcessOutcome, ProcessFailure> {
        let stdout_path = scratch.path.join("stdout");
        let stderr_path = scratch.path.join("stderr");
        let status_path = scratch.path.join("status");
        let timeout_ms = duration_milliseconds(timeout)?;
        let term_grace_ms = duration_milliseconds(TERM_GRACE)?;
        let command_program = PinnedFile::open(Path::new(command.get_program()), true)?;
        let python_descriptor = self.python.inherited_descriptor()?;
        let source_descriptor = self.source.inherited_descriptor()?;
        let command_descriptor = command_program.inherited_descriptor()?;
        let mut invocation = Command::new(descriptor_path(&python_descriptor));
        invocation
            .arg(descriptor_path(&source_descriptor))
            .arg("--timeout-ms")
            .arg(timeout_ms.to_string())
            .arg("--term-grace-ms")
            .arg(term_grace_ms.to_string())
            .arg("--stdout-cap")
            .arg(stdout_cap.to_string())
            .arg("--stderr-cap")
            .arg(stderr_cap.to_string())
            .arg("--stdout")
            .arg(&stdout_path)
            .arg("--stderr")
            .arg(&stderr_path)
            .arg("--status")
            .arg(&status_path)
            .arg("--")
            .arg(descriptor_path(&command_descriptor))
            .args(command.get_args())
            .stdout(Stdio::null());
        if let Some(directory) = command.get_current_dir() {
            invocation.current_dir(directory);
        }
        for (key, value) in command.get_envs() {
            if let Some(value) = value {
                invocation.env(key, value);
            } else {
                invocation.env_remove(key);
            }
        }
        let supervisor_status = invocation.status().map_err(|_| ProcessFailure::Spawn)?;
        self.python.verify()?;
        self.source.verify()?;
        command_program.verify()?;
        scratch.locate()?;
        let stdout_path = scratch.path.join("stdout");
        let stderr_path = scratch.path.join("stderr");
        let status_path = scratch.path.join("status");
        if supervisor_status.code() == Some(125) {
            return Err(ProcessFailure::Cleanup);
        }
        let stdout = read_capped(&stdout_path, stdout_cap)?;
        let stderr = read_capped(&stderr_path, stderr_cap)?;
        let status = read_capped(&status_path, STATUS_BYTE_CAP)?;
        let fields = parse_status(&status)?;
        let result = parse_result(required(&fields, "outcome")?)?;
        if supervisor_status.success() != (result == ProcessResult::Success) {
            return Err(ProcessFailure::Protocol);
        }
        let raw_wait_status = parse_i32(required(&fields, "raw_wait_status")?)?;
        if raw_wait_status < 0 {
            return Err(ProcessFailure::Protocol);
        }
        let outcome = ProcessOutcome {
            result,
            output: Output {
                status: ExitStatus::from_raw(raw_wait_status),
                stdout,
                stderr,
            },
            term_sent: parse_bool(required(&fields, "term_sent")?)?,
            kill_sent: parse_bool(required(&fields, "kill_sent")?)?,
            stdout_total: parse_usize(required(&fields, "stdout_total")?)?,
            stderr_total: parse_usize(required(&fields, "stderr_total")?)?,
            stdout_eof: parse_bool(required(&fields, "stdout_eof")?)?,
            stderr_eof: parse_bool(required(&fields, "stderr_eof")?)?,
            reaped_descendants: parse_usize(required(&fields, "reaped_descendants")?)?,
            observed_descendants: parse_usize(required(&fields, "observed_descendants")?)?,
            group_absent: parse_bool(required(&fields, "group_absent")?)?,
            descendants_absent: parse_bool(required(&fields, "descendants_absent")?)?,
        };
        let retained_stdout = parse_usize(required(&fields, "stdout_bytes")?)?;
        let retained_stderr = parse_usize(required(&fields, "stderr_bytes")?)?;
        if retained_stdout != outcome.output.stdout.len()
            || retained_stderr != outcome.output.stderr.len()
            || retained_stdout > stdout_cap
            || retained_stderr > stderr_cap
            || !outcome.group_absent
            || !outcome.descendants_absent
            || !outcome.stdout_eof
            || !outcome.stderr_eof
            || !required(&fields, "cleanup_error")?.is_empty()
        {
            return Err(ProcessFailure::Protocol);
        }
        Ok(outcome)
    }
}

impl PinnedFile {
    fn open(path: &Path, executable: bool) -> Result<Self, ProcessFailure> {
        let path = fs::canonicalize(path).map_err(|_| ProcessFailure::SupervisorIdentity)?;
        let metadata =
            fs::symlink_metadata(&path).map_err(|_| ProcessFailure::SupervisorIdentity)?;
        if !metadata.is_file()
            || metadata.file_type().is_symlink()
            || (executable && metadata.permissions().mode() & 0o111 == 0)
        {
            return Err(ProcessFailure::SupervisorIdentity);
        }
        let descriptor = rustix::fs::open(
            &path,
            OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::CLOEXEC,
            Mode::empty(),
        )
        .map_err(|_| ProcessFailure::SupervisorIdentity)?;
        let file = File::from(descriptor);
        let identity = identity_from_file(&file)?;
        if identity != file_identity(&path)? {
            return Err(ProcessFailure::SupervisorIdentity);
        }
        Ok(Self {
            path,
            file,
            identity,
            executable,
        })
    }

    fn verify(&self) -> Result<(), ProcessFailure> {
        let metadata =
            fs::symlink_metadata(&self.path).map_err(|_| ProcessFailure::SupervisorIdentity)?;
        if !metadata.is_file()
            || metadata.file_type().is_symlink()
            || (self.executable && metadata.permissions().mode() & 0o111 == 0)
            || identity_from_file(&self.file)? != self.identity
            || file_identity(&self.path)? != self.identity
        {
            return Err(ProcessFailure::SupervisorIdentity);
        }
        Ok(())
    }

    fn inherited_descriptor(&self) -> Result<OwnedFd, ProcessFailure> {
        dup(&self.file).map_err(|_| ProcessFailure::SupervisorIdentity)
    }

    fn read_bytes(&self) -> Result<Vec<u8>, ProcessFailure> {
        let mut file = self
            .file
            .try_clone()
            .map_err(|_| ProcessFailure::SupervisorIdentity)?;
        file.seek(SeekFrom::Start(0))
            .map_err(|_| ProcessFailure::SupervisorIdentity)?;
        let mut bytes = Vec::new();
        file.read_to_end(&mut bytes)
            .map_err(|_| ProcessFailure::SupervisorIdentity)?;
        Ok(bytes)
    }
}

fn descriptor_path(descriptor: &OwnedFd) -> PathBuf {
    PathBuf::from(format!("/proc/self/fd/{}", descriptor.as_raw_fd()))
}

fn identity_from_file(file: &File) -> Result<Identity, ProcessFailure> {
    let metadata = file
        .metadata()
        .map_err(|_| ProcessFailure::SupervisorIdentity)?;
    let mut reader = file
        .try_clone()
        .map_err(|_| ProcessFailure::SupervisorIdentity)?;
    reader
        .seek(SeekFrom::Start(0))
        .map_err(|_| ProcessFailure::SupervisorIdentity)?;
    let mut hasher = Sha256::new();
    let mut buffer = [0_u8; 64 * 1024];
    loop {
        let count = reader
            .read(&mut buffer)
            .map_err(|_| ProcessFailure::SupervisorIdentity)?;
        if count == 0 {
            break;
        }
        hasher.update(&buffer[..count]);
    }
    Ok(Identity {
        device: metadata.dev(),
        inode: metadata.ino(),
        length: metadata.len(),
        digest: hasher.finalize().into(),
    })
}

fn file_identity(path: &Path) -> Result<Identity, ProcessFailure> {
    let file = File::open(path).map_err(|_| ProcessFailure::SupervisorIdentity)?;
    identity_from_file(&file)
}

struct ScratchDirectory {
    parent: PathBuf,
    parent_device: u64,
    parent_inode: u64,
    device: u64,
    inode: u64,
    path: PathBuf,
    finished: bool,
}

impl ScratchDirectory {
    fn create(parent: &Path) -> Result<Self, ProcessFailure> {
        let parent_metadata = verified_scratch_directory(parent)?;
        let path = parent.join(format!(
            "process.{}.{}",
            std::process::id(),
            NEXT_SCRATCH.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).map_err(|_| ProcessFailure::Scratch)?;
        if fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).is_err() {
            let _ = fs::remove_dir(&path);
            return Err(ProcessFailure::Scratch);
        }
        let metadata = verified_scratch_directory(&path)?;
        Ok(Self {
            parent: parent.to_path_buf(),
            parent_device: parent_metadata.dev(),
            parent_inode: parent_metadata.ino(),
            device: metadata.dev(),
            inode: metadata.ino(),
            path,
            finished: false,
        })
    }

    fn locate(&mut self) -> Result<(), ProcessFailure> {
        let parent = verified_scratch_directory(&self.parent)?;
        if (parent.dev(), parent.ino()) != (self.parent_device, self.parent_inode) {
            return Err(ProcessFailure::Scratch);
        }
        let mut matches = Vec::new();
        for entry in fs::read_dir(&self.parent).map_err(|_| ProcessFailure::Scratch)? {
            let path = entry.map_err(|_| ProcessFailure::Scratch)?.path();
            let metadata = fs::symlink_metadata(&path).map_err(|_| ProcessFailure::Scratch)?;
            if (metadata.dev(), metadata.ino()) == (self.device, self.inode) {
                matches.push(path);
            }
        }
        if let [path] = matches.as_slice() {
            let metadata = verified_scratch_directory(path)?;
            if (metadata.dev(), metadata.ino()) != (self.device, self.inode) {
                return Err(ProcessFailure::Scratch);
            }
            self.path = path.clone();
            Ok(())
        } else {
            Err(ProcessFailure::Scratch)
        }
    }

    fn finish(mut self) -> Result<(), ProcessFailure> {
        self.locate()?;
        let clean = remove_scratch_tree(&self.path);
        let absent = fs::read_dir(&self.parent)
            .map_err(|_| ProcessFailure::Scratch)?
            .all(|entry| match entry {
                Ok(entry) => fs::symlink_metadata(entry.path()).is_ok_and(|metadata| {
                    (metadata.dev(), metadata.ino()) != (self.device, self.inode)
                }),
                Err(_) => false,
            });
        if !clean || !absent {
            return Err(ProcessFailure::Scratch);
        }
        self.finished = true;
        Ok(())
    }
}

impl Drop for ScratchDirectory {
    fn drop(&mut self) {
        if !self.finished {
            let _ = self.locate();
            let _ = remove_scratch_tree(&self.path);
        }
    }
}

fn verified_scratch_directory(path: &Path) -> Result<fs::Metadata, ProcessFailure> {
    let metadata = fs::symlink_metadata(path).map_err(|_| ProcessFailure::Scratch)?;
    if !metadata.is_dir()
        || metadata.file_type().is_symlink()
        || metadata.uid() != rustix::process::geteuid().as_raw()
        || metadata.permissions().mode() & 0o7777 != 0o700
    {
        return Err(ProcessFailure::Scratch);
    }
    Ok(metadata)
}

fn remove_scratch_tree(path: &Path) -> bool {
    let Ok(metadata) = fs::symlink_metadata(path) else {
        return false;
    };
    if metadata.is_dir() && !metadata.file_type().is_symlink() {
        let Ok(entries) = fs::read_dir(path) else {
            return false;
        };
        let mut clean = true;
        for entry in entries {
            match entry {
                Ok(entry) => clean &= remove_scratch_tree(&entry.path()),
                Err(_) => clean = false,
            }
        }
        clean &= fs::remove_dir(path).is_ok();
        clean
    } else {
        let expected = metadata.is_file() && !metadata.file_type().is_symlink();
        fs::remove_file(path).is_ok() && expected
    }
}

fn duration_milliseconds(duration: Duration) -> Result<u128, ProcessFailure> {
    let milliseconds = duration.as_millis();
    if milliseconds == 0 {
        Err(ProcessFailure::Protocol)
    } else {
        Ok(milliseconds)
    }
}

fn read_capped(path: &Path, cap: usize) -> Result<Vec<u8>, ProcessFailure> {
    let metadata = fs::symlink_metadata(path).map_err(|_| ProcessFailure::Protocol)?;
    if !metadata.is_file()
        || metadata.file_type().is_symlink()
        || metadata.permissions().mode() & 0o777 != 0o600
        || usize::try_from(metadata.len())
            .ok()
            .is_none_or(|length| length > cap)
    {
        return Err(ProcessFailure::Protocol);
    }
    fs::read(path).map_err(|_| ProcessFailure::Protocol)
}

fn parse_status(bytes: &[u8]) -> Result<BTreeMap<&str, &str>, ProcessFailure> {
    let text = std::str::from_utf8(bytes).map_err(|_| ProcessFailure::Protocol)?;
    let mut lines = text.split_terminator('\n');
    if lines.next() != Some(STATUS_MAGIC) || !text.ends_with('\n') {
        return Err(ProcessFailure::Protocol);
    }
    let mut fields = BTreeMap::new();
    for line in lines {
        let (key, value) = line.split_once('=').ok_or(ProcessFailure::Protocol)?;
        if fields.insert(key, value).is_some() {
            return Err(ProcessFailure::Protocol);
        }
    }
    let expected = [
        "cleanup_error",
        "descendants_absent",
        "exit_code",
        "exit_signal",
        "group_absent",
        "kill_sent",
        "observed_descendants",
        "outcome",
        "raw_wait_status",
        "reaped_descendants",
        "stderr_bytes",
        "stderr_eof",
        "stderr_total",
        "stdout_bytes",
        "stdout_eof",
        "stdout_total",
        "term_sent",
    ];
    if fields.keys().copied().collect::<Vec<_>>() != expected {
        return Err(ProcessFailure::Protocol);
    }
    Ok(fields)
}

fn required<'a>(fields: &'a BTreeMap<&str, &str>, key: &str) -> Result<&'a str, ProcessFailure> {
    fields.get(key).copied().ok_or(ProcessFailure::Protocol)
}

fn parse_result(value: &str) -> Result<ProcessResult, ProcessFailure> {
    match value {
        "success" => Ok(ProcessResult::Success),
        "nonzero-exit" => Ok(ProcessResult::NonzeroExit),
        "timeout" => Ok(ProcessResult::Timeout),
        "stdout-cap" => Ok(ProcessResult::StdoutCap),
        "stderr-cap" => Ok(ProcessResult::StderrCap),
        "live-descendant" => Ok(ProcessResult::LiveDescendant),
        "supervisor-signal" => Ok(ProcessResult::SupervisorSignal),
        "spawn-failure" => Ok(ProcessResult::SpawnFailure),
        _ => Err(ProcessFailure::Protocol),
    }
}

fn parse_bool(value: &str) -> Result<bool, ProcessFailure> {
    match value {
        "0" => Ok(false),
        "1" => Ok(true),
        _ => Err(ProcessFailure::Protocol),
    }
}

fn parse_usize(value: &str) -> Result<usize, ProcessFailure> {
    value.parse().map_err(|_| ProcessFailure::Protocol)
}

fn parse_i32(value: &str) -> Result<i32, ProcessFailure> {
    value.parse().map_err(|_| ProcessFailure::Protocol)
}

pub(crate) fn assert_process_failure_kills_drains_waits_and_reaps_the_group() {
    let root = std::env::temp_dir().join(format!(
        "legitimacy-process-supervisor-{}-{}",
        std::process::id(),
        NEXT_SCRATCH.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&root).unwrap();
    fs::set_permissions(&root, fs::Permissions::from_mode(0o700)).unwrap();
    let scratch_parent = root.join("processes");
    fs::create_dir(&scratch_parent).unwrap();
    fs::set_permissions(&scratch_parent, fs::Permissions::from_mode(0o700)).unwrap();
    let python = find_executable("python3").unwrap();
    let source = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("scripts/selected-authority-process-supervisor.py");
    let supervisor =
        ProcessSupervisor::new(python.clone(), source.clone(), scratch_parent.clone()).unwrap();

    let clean = run_shell(
        &supervisor,
        "printf clean-out; printf clean-err >&2",
        64,
        64,
    );
    assert_eq!(clean.result, ProcessResult::Success);
    assert_eq!(clean.output.stdout, b"clean-out");
    assert_eq!(clean.output.stderr, b"clean-err");
    assert!(clean.output.status.success());
    assert!(!clean.term_sent);
    assert!(!clean.kill_sent);
    assert_clean(&clean, 64, 64);

    let nonzero = run_shell(&supervisor, "printf rejected; exit 7", 64, 64);
    assert_eq!(nonzero.result, ProcessResult::NonzeroExit);
    assert_eq!(nonzero.output.status.code(), Some(7));
    assert_eq!(nonzero.output.stdout, b"rejected");
    assert_clean(&nonzero, 64, 64);

    let timeout = run_shell(&supervisor, "(while :; do sleep 1; done) & wait", 64, 64);
    assert_eq!(timeout.result, ProcessResult::Timeout);
    assert!(timeout.term_sent);
    assert!(!timeout.kill_sent);
    assert!(timeout.reaped_descendants >= 1);
    assert_clean(&timeout, 64, 64);

    let stdout_cap = run_shell(&supervisor, "while :; do printf 12345678; done", 31, 64);
    assert_eq!(stdout_cap.result, ProcessResult::StdoutCap);
    assert_eq!(stdout_cap.output.stdout.len(), 31);
    assert!(stdout_cap.stdout_total > 31);
    assert_clean(&stdout_cap, 31, 64);

    let stderr_cap = run_shell(&supervisor, "while :; do printf 12345678 >&2; done", 64, 29);
    assert_eq!(stderr_cap.result, ProcessResult::StderrCap);
    assert_eq!(stderr_cap.output.stderr.len(), 29);
    assert!(stderr_cap.stderr_total > 29);
    assert_clean(&stderr_cap, 64, 29);

    let live_descendant = run_shell(&supervisor, "(while :; do sleep 1; done) & exit 0", 64, 64);
    assert_eq!(live_descendant.result, ProcessResult::LiveDescendant);
    assert!(live_descendant.term_sent);
    assert!(live_descendant.reaped_descendants >= 1);
    assert_clean(&live_descendant, 64, 64);

    let term_resistant = run_shell(
        &supervisor,
        "trap '' TERM; (trap '' TERM; while :; do :; done) & wait",
        64,
        64,
    );
    assert_eq!(term_resistant.result, ProcessResult::Timeout);
    assert!(term_resistant.term_sent);
    assert!(term_resistant.kill_sent);
    assert!(term_resistant.reaped_descendants >= 1);
    assert_clean(&term_resistant, 64, 64);

    let preload = root.join("delayed-session.so");
    let compiler = Command::new("cc")
        .args(["-shared", "-fPIC", "-O2", "-Wall", "-Wextra", "-Werror"])
        .arg(
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("tests/fixtures/selected-authority-delayed-session.c"),
        )
        .arg("-o")
        .arg(&preload)
        .output()
        .unwrap();
    assert!(compiler.status.success(), "{compiler:?}");
    assert!(compiler.stdout.is_empty(), "{compiler:?}");
    assert!(compiler.stderr.is_empty(), "{compiler:?}");
    let mut delayed = Command::new("/bin/true");
    delayed
        .env("LD_PRELOAD", &preload)
        .env("LEGITIMACY_SESSION_DELAY_MICROSECONDS", "1500000");
    let started = Instant::now();
    let delayed = supervisor
        .run(&delayed, Duration::from_millis(100), 64, 64)
        .unwrap();
    assert_eq!(delayed.result, ProcessResult::Timeout);
    assert!(
        started.elapsed() < Duration::from_secs(13),
        "handshake cleanup exceeded its total publication budget: {:?}",
        started.elapsed()
    );
    assert_clean(&delayed, 64, 64);

    let detached_pid = root.join("detached.pid");
    let mut detached = Command::new(&python);
    detached
        .arg("-c")
        .arg(concat!(
            "import os,time\n",
            "FAILURE=70\n",
            "def close_quietly(descriptor):\n",
            " try:\n",
            "  os.close(descriptor)\n",
            " except OSError:\n",
            "  pass\n",
            "def write_all(descriptor,content):\n",
            " offset=0\n",
            " while offset<len(content):\n",
            "  count=os.write(descriptor,content[offset:])\n",
            "  if count<=0:\n",
            "   raise OSError('short write')\n",
            "  offset+=count\n",
            "readiness_read,readiness_write=os.pipe2(os.O_CLOEXEC)\n",
            "try:\n",
            " first_child=os.fork()\n",
            "except BaseException:\n",
            " close_quietly(readiness_read)\n",
            " close_quietly(readiness_write)\n",
            " os._exit(FAILURE)\n",
            "if first_child:\n",
            " close_quietly(readiness_write)\n",
            " frame=b''\n",
            " try:\n",
            "  while True:\n",
            "   chunk=os.read(readiness_read,2)\n",
            "   if not chunk:\n",
            "    break\n",
            "   frame+=chunk\n",
            "   if len(frame)>1:\n",
            "    break\n",
            " except BaseException:\n",
            "  frame=b''\n",
            " close_quietly(readiness_read)\n",
            " os._exit(0 if frame==b'R' else FAILURE)\n",
            "close_quietly(readiness_read)\n",
            "temporary=None\n",
            "try:\n",
            " os.setsid()\n",
            " second_child=os.fork()\n",
            " if second_child:\n",
            "  os.close(readiness_write)\n",
            "  os._exit(0)\n",
            " null=os.open('/dev/null',os.O_RDWR|os.O_CLOEXEC)\n",
            " try:\n",
            "  os.dup2(null,1)\n",
            "  os.dup2(null,2)\n",
            " finally:\n",
            "  os.close(null)\n",
            " pid=os.getpid()\n",
            " stat_descriptor=os.open('/proc/self/stat',os.O_RDONLY|os.O_CLOEXEC)\n",
            " try:\n",
            "  stat=b''\n",
            "  while True:\n",
            "   chunk=os.read(stat_descriptor,4096)\n",
            "   if not chunk:\n",
            "    break\n",
            "   stat+=chunk\n",
            "   if len(stat)>65536:\n",
            "    raise ValueError('oversized stat')\n",
            " finally:\n",
            "  os.close(stat_descriptor)\n",
            " closing=stat.rfind(b') ')\n",
            " fields=stat[closing+2:].split() if closing>=0 else []\n",
            " pid_text=str(pid)\n",
            " if not stat.startswith((pid_text+' (').encode('ascii')) or len(fields)<=19:\n",
            "  raise ValueError('malformed stat')\n",
            " start_text=fields[19].decode('ascii')\n",
            " start_time=int(start_text,10)\n",
            " if start_time<=0 or str(start_time)!=start_text:\n",
            "  raise ValueError('noncanonical start time')\n",
            " witness=('legitimacy.detached-process.v1\\npid='+pid_text+'\\nstart_time='+start_text+'\\n').encode('ascii')\n",
            " path=os.environ['DETACHED_PID_PATH']\n",
            " parent=os.path.dirname(path)\n",
            " temporary=os.path.join(parent,'.detached.pid.'+pid_text+'.tmp')\n",
            " file_flags=os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_CLOEXEC\n",
            " directory_flags=os.O_RDONLY|os.O_DIRECTORY|os.O_CLOEXEC\n",
            " if hasattr(os,'O_NOFOLLOW'):\n",
            "  file_flags|=os.O_NOFOLLOW\n",
            "  directory_flags|=os.O_NOFOLLOW\n",
            " directory_descriptor=os.open(parent,directory_flags)\n",
            " try:\n",
            "  marker_descriptor=os.open(temporary,file_flags,0o600)\n",
            "  try:\n",
            "   write_all(marker_descriptor,witness)\n",
            "   os.fsync(marker_descriptor)\n",
            "  finally:\n",
            "   os.close(marker_descriptor)\n",
            "  os.rename(temporary,path)\n",
            "  temporary=None\n",
            "  os.fsync(directory_descriptor)\n",
            " finally:\n",
            "  os.close(directory_descriptor)\n",
            " write_all(readiness_write,b'R')\n",
            " os.close(readiness_write)\n",
            " time.sleep(60)\n",
            "except BaseException:\n",
            " close_quietly(readiness_write)\n",
            " if temporary is not None:\n",
            "  try:\n",
            "   os.unlink(temporary)\n",
            "  except FileNotFoundError:\n",
            "   pass\n",
            " os._exit(71)\n",
        ))
        .env("DETACHED_PID_PATH", &detached_pid);
    let detached = supervisor
        .run(&detached, Duration::from_secs(1), 64, 64)
        .unwrap();
    assert_eq!(detached.result, ProcessResult::LiveDescendant);
    assert!(detached.observed_descendants >= 1);
    assert!(detached.reaped_descendants >= 1);
    assert_clean(&detached, 64, 64);
    let detached_witness = fs::read_to_string(detached_pid).unwrap();
    let witness_lines = detached_witness
        .strip_suffix('\n')
        .expect("detached-process witness must have a final LF")
        .split('\n')
        .collect::<Vec<_>>();
    assert_eq!(
        witness_lines.len(),
        3,
        "detached-process witness must contain exactly three lines"
    );
    assert_eq!(
        witness_lines[0], "legitimacy.detached-process.v1",
        "detached-process witness must contain the exact versioned magic"
    );
    let witnessed_pid_text = witness_lines[1]
        .strip_prefix("pid=")
        .expect("detached-process witness must contain a PID field");
    let witnessed_pid = witnessed_pid_text
        .parse::<i32>()
        .expect("detached-process PID must be in range");
    assert!(witnessed_pid > 0, "detached-process PID must be positive");
    assert_eq!(
        witnessed_pid.to_string(),
        witnessed_pid_text,
        "detached-process PID must be canonical decimal"
    );
    let witnessed_start_time_text = witness_lines[2]
        .strip_prefix("start_time=")
        .expect("detached-process witness must contain a start-time field");
    let witnessed_start_time = witnessed_start_time_text
        .parse::<u64>()
        .expect("detached-process start time must be in range");
    assert!(
        witnessed_start_time > 0,
        "detached-process start time must be positive"
    );
    assert_eq!(
        witnessed_start_time.to_string(),
        witnessed_start_time_text,
        "detached-process start time must be canonical decimal"
    );
    let witnessed_stat = Path::new("/proc")
        .join(witnessed_pid.to_string())
        .join("stat");
    match fs::read_to_string(&witnessed_stat) {
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => panic!("failed to prove detached-process identity absence: {error}"),
        Ok(stat) => {
            let expected_prefix = format!("{witnessed_pid} (");
            assert!(
                stat.starts_with(&expected_prefix),
                "live /proc stat has a mismatched PID field"
            );
            let closing = stat
                .rfind(") ")
                .expect("live /proc stat must contain a closing command delimiter");
            assert!(
                closing >= expected_prefix.len(),
                "live /proc stat has a malformed command field"
            );
            let fields = stat[closing + 2..]
                .split_ascii_whitespace()
                .collect::<Vec<_>>();
            let current_start_time_text = fields
                .get(19)
                .expect("live /proc stat must contain a start-time field");
            let current_start_time = current_start_time_text
                .parse::<u64>()
                .expect("live /proc start time must be in range");
            assert_eq!(
                current_start_time.to_string(),
                *current_start_time_text,
                "live /proc start time must be canonical decimal"
            );
            assert_ne!(
                current_start_time, witnessed_start_time,
                "witnessed detached-process identity is still live"
            );
        }
    }

    let nested = root.join("nested");
    fs::create_dir(&nested).unwrap();
    fs::set_permissions(&nested, fs::Permissions::from_mode(0o700)).unwrap();
    let mut nested_command = Command::new(&python);
    nested_command
        .arg(&source)
        .args([
            "--timeout-ms",
            "5000",
            "--term-grace-ms",
            "100",
            "--stdout-cap",
            "64",
            "--stderr-cap",
            "64",
            "--stdout",
        ])
        .arg(nested.join("stdout"))
        .arg("--stderr")
        .arg(nested.join("stderr"))
        .arg("--status")
        .arg(nested.join("status"))
        .args([
            "--",
            "/bin/sh",
            "-c",
            "trap '' TERM; kill -TERM \"$PPID\"; while :; do sleep 1; done",
        ]);
    let nested_outcome = supervisor
        .run(&nested_command, Duration::from_secs(3), 64, 64)
        .unwrap();
    assert_eq!(nested_outcome.result, ProcessResult::NonzeroExit);
    assert_clean(&nested_outcome, 64, 64);
    let nested_status = fs::read_to_string(nested.join("status")).unwrap();
    assert!(nested_status.contains("outcome=supervisor-signal\n"));
    assert!(nested_status.contains("descendants_absent=1\n"));
    fs::remove_dir_all(&nested).unwrap();

    let rename_parent = scratch_parent.clone();
    let mut rename = Command::new(&python);
    rename
        .arg("-c")
        .arg(concat!(
            "import os\n",
            "p=os.environ['PROCESS_PARENT']\n",
            "n=next(x for x in os.listdir(p) if x.startswith('process.'))\n",
            "os.rename(os.path.join(p,n),os.path.join(p,'renamed-process'))\n",
        ))
        .env("PROCESS_PARENT", &rename_parent);
    let renamed = supervisor
        .run(&rename, Duration::from_secs(1), 64, 64)
        .unwrap();
    assert_eq!(renamed.result, ProcessResult::Success);
    assert_clean(&renamed, 64, 64);

    let mut special = Command::new(&python);
    special
        .arg("-c")
        .arg(concat!(
            "import os\n",
            "p=os.environ['PROCESS_PARENT']\n",
            "n=next(x for x in os.listdir(p) if x.startswith('process.'))\n",
            "os.mkfifo(os.path.join(p,n,'unexpected'))\n",
        ))
        .env("PROCESS_PARENT", &scratch_parent);
    assert!(matches!(
        supervisor.run(&special, Duration::from_secs(1), 64, 64),
        Err(ProcessFailure::Cleanup)
    ));

    let limited = root.join("limited");
    fs::create_dir(&limited).unwrap();
    fs::set_permissions(&limited, fs::Permissions::from_mode(0o700)).unwrap();
    let command_text = format!(
        "ulimit -f 0; exec {} {} --timeout-ms 1000 --term-grace-ms 100 --stdout-cap 64 --stderr-cap 64 --stdout {} --stderr {} --status {} -- /bin/true",
        python.display(),
        source.display(),
        limited.join("stdout").display(),
        limited.join("stderr").display(),
        limited.join("status").display(),
    );
    let mut io_failure = Command::new("/bin/sh");
    io_failure.args(["-c", &command_text]);
    let io_failure = supervisor
        .run(&io_failure, Duration::from_secs(3), 1024, 1024)
        .unwrap();
    assert_eq!(io_failure.result, ProcessResult::NonzeroExit);
    assert_eq!(io_failure.output.status.code(), Some(125));
    assert_clean(&io_failure, 1024, 1024);
    fs::remove_dir_all(&limited).unwrap();

    assert_eq!(fs::read_dir(&scratch_parent).unwrap().count(), 0);
    fs::remove_dir_all(root).unwrap();
}

fn run_shell(
    supervisor: &ProcessSupervisor,
    script: &str,
    stdout_cap: usize,
    stderr_cap: usize,
) -> ProcessOutcome {
    let mut command = Command::new("/bin/sh");
    command.args(["-c", script]);
    supervisor
        .run(&command, Duration::from_millis(100), stdout_cap, stderr_cap)
        .unwrap()
}

fn assert_clean(outcome: &ProcessOutcome, stdout_cap: usize, stderr_cap: usize) {
    assert!(outcome.group_absent);
    assert!(outcome.descendants_absent);
    assert!(outcome.stdout_eof);
    assert!(outcome.stderr_eof);
    assert!(outcome.output.stdout.len() <= stdout_cap);
    assert!(outcome.output.stderr.len() <= stderr_cap);
}

fn find_executable(name: &str) -> Option<PathBuf> {
    std::env::split_paths(&std::env::var_os("PATH")?).find_map(|directory| {
        let path = directory.join(name);
        fs::metadata(&path)
            .ok()
            .filter(|metadata| metadata.is_file() && metadata.permissions().mode() & 0o111 != 0)
            .and_then(|_| fs::canonicalize(path).ok())
    })
}
