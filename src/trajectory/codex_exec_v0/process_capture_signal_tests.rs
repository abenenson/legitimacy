use super::super::cleanup::{RealSupervisorOperations, SupervisorOperations, cleanup_process_tree};
use super::super::supervisor::{
    PidfdReceiptFaultRequestTestOnly, PidfdReceiptFaultTestOnly,
    execute_held_pidfd_receipt_fault_test_only,
};
use super::*;
use std::fs;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::PermissionsExt;
use std::process::{Child, Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

#[derive(Debug, Eq, PartialEq)]
struct SigchldSnapshot {
    blocked: bool,
    handler: usize,
    flags: libc::c_int,
    mask: Vec<bool>,
}

fn sigchld_snapshot() -> SigchldSnapshot {
    unsafe {
        let mut current_mask = std::mem::zeroed();
        assert_eq!(
            libc::pthread_sigmask(libc::SIG_BLOCK, std::ptr::null(), &mut current_mask),
            0
        );
        let mut action = std::mem::zeroed();
        assert_eq!(
            libc::sigaction(libc::SIGCHLD, std::ptr::null(), &mut action),
            0
        );
        SigchldSnapshot {
            blocked: libc::sigismember(&current_mask, libc::SIGCHLD) == 1,
            handler: action.sa_sigaction,
            // Linux may add its private SA_RESTORER bit when an otherwise
            // identical action is reinstalled through libc.
            flags: action.sa_flags & !0x0400_0000,
            mask: (1..=64)
                .map(|signal| libc::sigismember(&action.sa_mask, signal) == 1)
                .collect(),
        }
    }
}

struct EscapeOperations {
    real: RealSupervisorOperations,
    go: std::path::PathBuf,
    escaped: std::path::PathBuf,
    ready: std::path::PathBuf,
    escaped_pid: Option<i32>,
    term_excluded_escape: bool,
    kill_before_reparent: bool,
    kill_after_reparent: bool,
}

impl EscapeOperations {
    fn synchronize_escape(&mut self) -> AdapterResultV0<()> {
        if self.escaped_pid.is_some() {
            return Ok(());
        }
        fs::write(&self.go, b"go").map_err(|_| error(AdapterErrorCodeV0::CaptureCleanup))?;
        let deadline = Instant::now() + Duration::from_secs(2);
        while !self.ready.exists() && Instant::now() < deadline {
            std::thread::yield_now();
        }
        if !self.ready.exists() {
            return Err(error(AdapterErrorCodeV0::CaptureCleanup));
        }
        let pid = fs::read_to_string(&self.escaped)
            .map_err(|_| error(AdapterErrorCodeV0::CaptureCleanup))?
            .trim()
            .parse()
            .map_err(|_| error(AdapterErrorCodeV0::CaptureCleanup))?;
        let process =
            Pid::from_raw(pid).ok_or_else(|| error(AdapterErrorCodeV0::CaptureCleanup))?;
        if rustix::process::getsid(Some(process)) != Ok(process) {
            return Err(error(AdapterErrorCodeV0::CaptureCleanup));
        }
        self.escaped_pid = Some(pid);
        Ok(())
    }
}

impl SupervisorOperations for EscapeOperations {
    fn observe(&mut self, owned: &mut OwnedChildren) -> AdapterResultV0<()> {
        self.real.observe(owned)
    }

    fn signal(&mut self, owned: &OwnedChildren, signal: Signal) -> AdapterResultV0<()> {
        if signal == Signal::TERM && self.escaped_pid.is_none() {
            self.synchronize_escape()?;
            let escaped = self.escaped_pid.expect("escape synchronized");
            self.term_excluded_escape = !owned.contains_pid(escaped);
        }
        if signal == Signal::KILL {
            let escaped = self.escaped_pid.expect("escape synchronized");
            if owned.contains_pid(escaped) {
                self.kill_after_reparent = true;
            } else {
                self.kill_before_reparent = true;
            }
        }
        self.real.signal(owned, signal)
    }

    fn try_wait(&mut self, child: &mut Child) -> AdapterResultV0<Option<ExitStatus>> {
        self.real.try_wait(child)
    }

    fn reap(&mut self, owned: &mut OwnedChildren) -> AdapterResultV0<()> {
        self.real.reap(owned)
    }

    fn absent(&mut self, owned: &mut OwnedChildren) -> AdapterResultV0<bool> {
        self.real.absent(owned)
    }

    fn sleep(&mut self, _duration: Duration) {
        std::thread::yield_now();
    }
}

#[test]
#[serial_test::serial]
fn post_observation_setsid_escape_is_owned_killed_reaped_and_absent() {
    const HELPER: &str = "LEGITIMACY_SIGNAL_ESCAPE_HELPER";
    if std::env::var_os(HELPER).is_none() {
        let result = Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "trajectory::codex_exec_v0::process_capture::platform::signal::tests::post_observation_setsid_escape_is_owned_killed_reaped_and_absent",
                "--nocapture",
                "--test-threads=1",
            ])
            .env(HELPER, "1")
            .status()
            .unwrap();
        assert!(result.success());
        return;
    }

    let root =
        std::env::temp_dir().join(format!("legitimacy-signal-escape-{}", std::process::id()));
    fs::create_dir(&root).unwrap();
    fs::set_permissions(&root, fs::Permissions::from_mode(0o700)).unwrap();
    let go = root.join("go");
    let escaped = root.join("escaped-pid");
    let ready = root.join("escaped-ready");

    let previous_subreaper = rustix::process::child_subreaper().unwrap();
    rustix::process::set_child_subreaper(Pid::from_raw(1)).unwrap();
    let mut child = Command::new("/bin/sh")
        .args([
            "-c",
            "trap '' TERM; while [ ! -e \"$1\" ]; do :; done; /usr/bin/setsid /bin/sh -c 'trap \"\" TERM; printf \"%s\\n\" \"$$\" > \"$1\"; : > \"$2\"; while :; do :; done' sh \"$2\" \"$3\" & while :; do :; done",
            "sh",
        ])
        .arg(&go)
        .arg(&escaped)
        .arg(&ready)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    let pid = Pid::from_raw(i32::try_from(child.id()).unwrap()).unwrap();
    let pidfd = pidfd_open(pid, PidfdFlags::empty()).unwrap();
    let mut owned = OwnedChildren::new(child.id(), pidfd);
    let mut operations = EscapeOperations {
        real: RealSupervisorOperations,
        go,
        escaped: escaped.clone(),
        ready,
        escaped_pid: None,
        term_excluded_escape: false,
        kill_before_reparent: false,
        kill_after_reparent: false,
    };
    let mut status = None;
    cleanup_process_tree(&mut operations, &mut child, &mut status, &mut owned).unwrap();
    let escaped_pid = operations.escaped_pid.unwrap();
    if !operations.kill_after_reparent {
        let escaped = Pid::from_raw(escaped_pid).unwrap();
        let escaped_pidfd = pidfd_open(escaped, PidfdFlags::empty()).unwrap();
        pidfd_send_signal(&escaped_pidfd, Signal::KILL).unwrap();
        waitid(WaitId::PidFd(escaped_pidfd.as_fd()), WaitIdOptions::EXITED).unwrap();
    }
    assert!(operations.term_excluded_escape);
    assert!(operations.kill_before_reparent);
    assert!(operations.kill_after_reparent);
    assert!(status.is_some());
    assert_eq!(owned.len(), 0);
    assert!(!std::path::Path::new(&format!("/proc/{escaped_pid}")).exists());
    assert!(direct_child_pids().unwrap().is_empty());
    rustix::process::set_child_subreaper(previous_subreaper).unwrap();
    fs::remove_dir_all(root).unwrap();
}

#[test]
#[serial_test::serial]
fn post_spawn_failure_after_owned_receipt_cleans_escape_before_restoration() {
    const HELPER: &str = "LEGITIMACY_PIDFD_RECEIPT_FAILURE_HELPER";
    if std::env::var_os(HELPER).is_none() {
        let result = Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "trajectory::codex_exec_v0::process_capture::platform::signal::tests::post_spawn_failure_after_owned_receipt_cleans_escape_before_restoration",
                "--nocapture",
                "--test-threads=1",
            ])
            .env(HELPER, "1")
            .status()
            .unwrap();
        assert!(result.success());
        return;
    }

    let root =
        std::env::temp_dir().join(format!("legitimacy-signal-receipt-{}", std::process::id()));
    fs::create_dir(&root).unwrap();
    fs::set_permissions(&root, fs::Permissions::from_mode(0o700)).unwrap();
    let helper_path = root.join("helper");
    fs::copy("/bin/sh", &helper_path).unwrap();
    fs::set_permissions(&helper_path, fs::Permissions::from_mode(0o700)).unwrap();
    let workspace_path = root.join("workspace");
    fs::create_dir(&workspace_path).unwrap();
    fs::set_permissions(&workspace_path, fs::Permissions::from_mode(0o700)).unwrap();
    let helper = HeldFile::open(&helper_path, FileRole::Executable).unwrap();
    let workspace = std::fs::File::open(&workspace_path).unwrap();
    let main_pid_path = root.join("main-pid");
    let escaped_pid_path = root.join("escaped-pid");
    let ready = root.join("ready");
    let signal_before = sigchld_snapshot();
    let subreaper_before = rustix::process::child_subreaper().unwrap();
    let script = b"trap '' TERM; printf '%s\n' \"$$\" > \"$1\"; /usr/bin/setsid /bin/sh -c 'trap \"\" TERM; printf \"%s\\n\" \"$$\" > \"$1\"; : > \"$2\"; while :; do :; done' sh \"$2\" \"$3\" & while [ ! -e \"$3\" ]; do :; done; while :; do :; done";
    let error = match execute_held_pidfd_receipt_fault_test_only(
        &helper,
        &workspace,
        b"",
        Duration::from_secs(2),
        64,
        64,
        PidfdReceiptFaultRequestTestOnly {
            argv: &[
                b"sh",
                b"-c",
                script,
                b"sh",
                main_pid_path.as_os_str().as_bytes(),
                escaped_pid_path.as_os_str().as_bytes(),
                ready.as_os_str().as_bytes(),
            ],
            ready: ready.clone(),
            fault: PidfdReceiptFaultTestOnly::FailureAfterOwnedReceipt,
        },
    ) {
        Ok(_) => panic!("post-spawn receipt fault must fail"),
        Err(error) => error,
    };
    assert_eq!(error.code(), AdapterErrorCodeV0::CaptureSpawn);
    let main_pid = fs::read_to_string(main_pid_path).unwrap();
    let escaped_pid = fs::read_to_string(escaped_pid_path).unwrap();
    for pid in [main_pid.trim(), escaped_pid.trim()] {
        assert!(!std::path::Path::new(&format!("/proc/{pid}")).exists());
    }
    assert!(direct_child_pids().unwrap().is_empty());
    assert_eq!(
        rustix::process::child_subreaper().unwrap(),
        subreaper_before
    );
    assert_eq!(sigchld_snapshot(), signal_before);
    fs::remove_dir_all(root).unwrap();
}

fn exercise_pre_exec_receipt_rejection(label: &str, fault: PidfdReceiptFaultTestOnly) -> Duration {
    let root = std::env::temp_dir().join(format!(
        "legitimacy-signal-receipt-{label}-{}",
        std::process::id()
    ));
    fs::create_dir(&root).unwrap();
    fs::set_permissions(&root, fs::Permissions::from_mode(0o700)).unwrap();
    let helper_path = root.join("helper");
    fs::copy("/bin/sh", &helper_path).unwrap();
    fs::set_permissions(&helper_path, fs::Permissions::from_mode(0o700)).unwrap();
    let workspace_path = root.join("workspace");
    fs::create_dir(&workspace_path).unwrap();
    fs::set_permissions(&workspace_path, fs::Permissions::from_mode(0o700)).unwrap();
    let helper = HeldFile::open(&helper_path, FileRole::Executable).unwrap();
    let workspace = std::fs::File::open(&workspace_path).unwrap();
    let main_pid_path = root.join("main-pid");
    let escaped_pid_path = root.join("escaped-pid");
    let ready = root.join("ready");
    let signal_before = sigchld_snapshot();
    let subreaper_before = rustix::process::child_subreaper().unwrap();
    let script = b"trap '' TERM; printf '%s\n' \"$$\" > \"$1\"; /usr/bin/setsid /bin/sh -c 'trap \"\" TERM; printf \"%s\\n\" \"$$\" > \"$1\"; : > \"$2\"; while :; do :; done' sh \"$2\" \"$3\" & while [ ! -e \"$3\" ]; do :; done; while :; do :; done";
    let started = Instant::now();
    let error = match execute_held_pidfd_receipt_fault_test_only(
        &helper,
        &workspace,
        b"",
        Duration::from_secs(2),
        64,
        64,
        PidfdReceiptFaultRequestTestOnly {
            argv: &[
                b"sh",
                b"-c",
                script,
                b"sh",
                main_pid_path.as_os_str().as_bytes(),
                escaped_pid_path.as_os_str().as_bytes(),
                ready.as_os_str().as_bytes(),
            ],
            ready: ready.clone(),
            fault,
        },
    ) {
        Ok(_) => panic!("receipt shape fault must fail"),
        Err(error) => error,
    };
    let elapsed = started.elapsed();
    assert_eq!(error.code(), AdapterErrorCodeV0::CaptureSpawn);
    assert!(!main_pid_path.exists());
    assert!(!escaped_pid_path.exists());
    assert!(!ready.exists());
    assert!(direct_child_pids().unwrap().is_empty());
    assert_eq!(
        rustix::process::child_subreaper().unwrap(),
        subreaper_before
    );
    assert_eq!(sigchld_snapshot(), signal_before);
    fs::remove_dir_all(root).unwrap();
    elapsed
}

fn run_bounded_receipt_shape_subprocess(test_name: &str, helper_variable: &str) {
    if std::env::var_os(helper_variable).is_some() {
        return;
    }
    let result = Command::new("/usr/bin/timeout")
        .args(["--signal=KILL", "12s"])
        .arg(std::env::current_exe().unwrap())
        .args(["--exact", test_name, "--nocapture", "--test-threads=1"])
        .env(helper_variable, "1")
        .status()
        .unwrap();
    assert!(result.success());
}

#[test]
#[serial_test::serial]
fn permanent_non_eintr_receipt_error_prevents_exec_and_restores_boundary() {
    const HELPER: &str = "LEGITIMACY_PIDFD_PERMANENT_RECEIVE_ERROR_HELPER";
    const TEST: &str = "trajectory::codex_exec_v0::process_capture::platform::signal::tests::permanent_non_eintr_receipt_error_prevents_exec_and_restores_boundary";
    run_bounded_receipt_shape_subprocess(TEST, HELPER);
    if std::env::var_os(HELPER).is_none() {
        return;
    }
    let elapsed = exercise_pre_exec_receipt_rejection(
        "permanent-error",
        PidfdReceiptFaultTestOnly::PermanentReceiveErrorBeforeExec,
    );
    assert!(elapsed < Duration::from_secs(8));
}

#[test]
#[serial_test::serial]
fn consumed_handleless_receipt_packet_prevents_exec_and_restores_boundary() {
    const HELPER: &str = "LEGITIMACY_PIDFD_HANDLELESS_PACKET_HELPER";
    const TEST: &str = "trajectory::codex_exec_v0::process_capture::platform::signal::tests::consumed_handleless_receipt_packet_prevents_exec_and_restores_boundary";
    run_bounded_receipt_shape_subprocess(TEST, HELPER);
    if std::env::var_os(HELPER).is_none() {
        return;
    }
    let elapsed = exercise_pre_exec_receipt_rejection(
        "handleless-packet",
        PidfdReceiptFaultTestOnly::HandlelessPacketBeforeExec,
    );
    assert!(elapsed < Duration::from_secs(8));
}

#[test]
#[serial_test::serial]
fn unavailable_fallback_cannot_cross_the_owned_receipt_exec_handshake() {
    const HELPER: &str = "LEGITIMACY_PIDFD_FALLBACK_ACQUISITION_FAILURE_HELPER";
    const TEST: &str = "trajectory::codex_exec_v0::process_capture::platform::signal::tests::unavailable_fallback_cannot_cross_the_owned_receipt_exec_handshake";
    run_bounded_receipt_shape_subprocess(TEST, HELPER);
    if std::env::var_os(HELPER).is_none() {
        return;
    }
    let elapsed = exercise_pre_exec_receipt_rejection(
        "fallback-acquisition-failure",
        PidfdReceiptFaultTestOnly::FallbackAcquisitionFailureBeforeExec,
    );
    assert!(elapsed < Duration::from_secs(8));
}
