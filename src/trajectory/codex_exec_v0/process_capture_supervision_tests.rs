use super::super::cleanup::{RealSupervisorOperations, SupervisorOperations, cleanup_process_tree};
use super::super::signal::OwnedChildren;
use super::super::supervision::{
    PrimaryPublicationOrderingTestOnly, WriterReleaseConditionTestOnly, WriterStartControlTestOnly,
    closed_failure_observation_control, pipe_join_fault_control,
};
use super::super::supervisor::{
    WriterControlledExecutionRequestTestOnly, execute_held_test_only,
    execute_held_with_writer_start_control_test_only,
};
use super::*;
use std::process::ExitStatus;
use std::time::Instant;

#[derive(Clone, Copy, Eq, PartialEq)]
enum CleanupFault {
    Observe,
    Signal,
    TryWait,
    Reap,
    Absence,
}

struct FaultSupervisorOperations {
    fault: CleanupFault,
    injected: bool,
    order: Vec<&'static str>,
    cycle_observed: bool,
    cycle_reaped: bool,
    status_known: bool,
    absence_proved: bool,
    signal_after_absence_proof: bool,
    real: RealSupervisorOperations,
}

impl FaultSupervisorOperations {
    fn inject(&mut self, stage: CleanupFault) -> AdapterResultV0<()> {
        if self.fault == stage && !self.injected {
            self.injected = true;
            Err(error(AdapterErrorCodeV0::CaptureCleanup))
        } else {
            Ok(())
        }
    }
}

impl SupervisorOperations for FaultSupervisorOperations {
    fn observe(&mut self, owned: &mut OwnedChildren) -> AdapterResultV0<()> {
        self.order.push("observe");
        self.cycle_observed = false;
        self.cycle_reaped = false;
        self.real.observe(owned)?;
        let result = self.inject(CleanupFault::Observe);
        self.cycle_observed = result.is_ok();
        result
    }

    fn signal(
        &mut self,
        owned: &OwnedChildren,
        signal: rustix::process::Signal,
    ) -> AdapterResultV0<()> {
        if self.absence_proved {
            self.signal_after_absence_proof = true;
        }
        self.order.push(if signal == rustix::process::Signal::TERM {
            "signal-term"
        } else {
            "signal-kill"
        });
        self.real.signal(owned, signal)?;
        self.inject(CleanupFault::Signal)
    }

    fn try_wait(&mut self, child: &mut std::process::Child) -> AdapterResultV0<Option<ExitStatus>> {
        self.order.push("try-wait");
        let result = self.real.try_wait(child)?;
        let injected = self.inject(CleanupFault::TryWait);
        if injected.is_ok() && result.is_some() {
            self.status_known = true;
        }
        injected?;
        Ok(result)
    }

    fn reap(&mut self, owned: &mut OwnedChildren) -> AdapterResultV0<()> {
        self.order.push("reap");
        self.real.reap(owned)?;
        let result = self.inject(CleanupFault::Reap);
        self.cycle_reaped = result.is_ok();
        result
    }

    fn absent(&mut self, owned: &mut OwnedChildren) -> AdapterResultV0<bool> {
        self.order.push("absence");
        let result = self.real.absent(owned)?;
        self.inject(CleanupFault::Absence)?;
        if result && self.cycle_observed && self.cycle_reaped && self.status_known {
            self.absence_proved = true;
        }
        Ok(result)
    }

    fn sleep(&mut self, _duration: Duration) {
        std::thread::yield_now();
    }
}

#[test]
fn cleanup_faults_stay_sticky_but_recovered_absence_stops_signaling() {
    for fault in [
        CleanupFault::Observe,
        CleanupFault::Signal,
        CleanupFault::TryWait,
        CleanupFault::Reap,
        CleanupFault::Absence,
    ] {
        let mut child = Command::new("/bin/true").spawn().unwrap();
        let pid = rustix::process::Pid::from_raw(i32::try_from(child.id()).unwrap()).unwrap();
        let pidfd = rustix::process::pidfd_open(pid, rustix::process::PidfdFlags::empty()).unwrap();
        let reaped_status = child.wait().unwrap();
        let mut operations = FaultSupervisorOperations {
            fault,
            injected: false,
            order: Vec::new(),
            cycle_observed: false,
            cycle_reaped: false,
            status_known: fault != CleanupFault::TryWait,
            absence_proved: false,
            signal_after_absence_proof: false,
            real: RealSupervisorOperations,
        };
        let mut status = if fault == CleanupFault::TryWait {
            None
        } else {
            Some(reaped_status)
        };
        let mut owned = OwnedChildren::new(child.id(), pidfd);
        let started = Instant::now();
        let error =
            cleanup_process_tree(&mut operations, &mut child, &mut status, &mut owned).unwrap_err();
        assert_eq!(error.code(), AdapterErrorCodeV0::CaptureCleanup);
        assert!(started.elapsed() < Duration::from_secs(1));
        assert_eq!(operations.order.first(), Some(&"observe"));
        assert_eq!(operations.order.get(1), Some(&"signal-term"));
        assert!(operations.injected);
        assert!(operations.absence_proved);
        assert!(!operations.signal_after_absence_proof);
        assert!(!operations.order.contains(&"signal-kill"));
        assert_eq!(operations.order.last(), Some(&"absence"));
        assert!(status.is_some());
        assert!(operations.real.absent(&mut owned).unwrap());
        assert!(child.try_wait().unwrap().is_some());
    }
}

struct RecordingSupervisorOperations {
    order: Vec<&'static str>,
    real: RealSupervisorOperations,
}

impl SupervisorOperations for RecordingSupervisorOperations {
    fn observe(&mut self, owned: &mut OwnedChildren) -> AdapterResultV0<()> {
        self.order.push("observe");
        self.real.observe(owned)
    }

    fn signal(
        &mut self,
        owned: &OwnedChildren,
        signal: rustix::process::Signal,
    ) -> AdapterResultV0<()> {
        self.order.push(if signal == rustix::process::Signal::TERM {
            "signal-term"
        } else {
            "signal-kill"
        });
        self.real.signal(owned, signal)
    }

    fn try_wait(&mut self, child: &mut std::process::Child) -> AdapterResultV0<Option<ExitStatus>> {
        self.order.push("try-wait");
        self.real.try_wait(child)
    }

    fn reap(&mut self, owned: &mut OwnedChildren) -> AdapterResultV0<()> {
        self.order.push("reap");
        self.real.reap(owned)
    }

    fn absent(&mut self, owned: &mut OwnedChildren) -> AdapterResultV0<bool> {
        self.order.push("absence");
        self.real.absent(owned)
    }

    fn sleep(&mut self, _duration: Duration) {
        std::thread::yield_now();
    }
}

#[test]
fn live_term_resistant_tree_reaches_kill_and_finishes_boundedly() {
    let root = private_test_root("cleanup-kill-escalation");
    let ready = root.join("ready");
    let mut child = Command::new("/usr/bin/setsid")
        .args([
            "/bin/sh",
            "-c",
            "trap '' TERM; : > \"$1\"; while :; do :; done",
            "sh",
        ])
        .arg(&ready)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    let ready_deadline = Instant::now() + Duration::from_secs(2);
    while !ready.exists() && Instant::now() < ready_deadline {
        std::thread::sleep(Duration::from_millis(5));
    }
    assert!(ready.exists());

    let pid = rustix::process::Pid::from_raw(i32::try_from(child.id()).unwrap()).unwrap();
    let pidfd = rustix::process::pidfd_open(pid, rustix::process::PidfdFlags::empty()).unwrap();
    let mut operations = RecordingSupervisorOperations {
        order: Vec::new(),
        real: RealSupervisorOperations,
    };
    let mut status = None;
    let mut owned = OwnedChildren::new(child.id(), pidfd);
    let started = Instant::now();
    cleanup_process_tree(&mut operations, &mut child, &mut status, &mut owned).unwrap();
    assert!(started.elapsed() < Duration::from_secs(2));
    let first_term = operations
        .order
        .iter()
        .position(|operation| *operation == "signal-term")
        .unwrap();
    let first_kill = operations
        .order
        .iter()
        .position(|operation| *operation == "signal-kill")
        .unwrap();
    assert!(first_term < first_kill);
    assert!(status.is_some());
    assert!(operations.real.absent(&mut owned).unwrap());
    assert!(child.try_wait().unwrap().is_some());
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn pipe_worker_failure_still_joins_every_created_worker_boundedly() {
    let (joined, uncertain, elapsed) = pipe_join_fault_control();
    assert_eq!(joined, 3);
    assert!(uncertain);
    assert!(elapsed < Duration::from_secs(1));
}

#[test]
fn cleanup_closes_late_worker_facts_before_primary_selection() {
    assert_eq!(
        closed_failure_observation_control(
            PrimaryPublicationOrderingTestOnly::BeforeCleanup,
            false,
        ),
        AdapterErrorCodeV0::CaptureStdoutOverflow,
        "favorable ordering"
    );
    assert_eq!(
        closed_failure_observation_control(
            PrimaryPublicationOrderingTestOnly::AfterCancellation,
            false,
        ),
        AdapterErrorCodeV0::CaptureStdoutOverflow,
        "higher-ranked worker fact published during cleanup"
    );
    assert_eq!(
        closed_failure_observation_control(
            PrimaryPublicationOrderingTestOnly::AfterCancellation,
            true,
        ),
        AdapterErrorCodeV0::CaptureCleanup,
        "cleanup uncertainty remains dominant"
    );
}

#[test]
#[serial_test::serial]
fn early_stdin_close_with_proven_empty_tree_is_capture_stdin() {
    let root = private_test_root("controlled-early-stdin-close");
    let helper_path = root.join("helper");
    fs::copy("/bin/sh", &helper_path).unwrap();
    fs::set_permissions(&helper_path, fs::Permissions::from_mode(0o700)).unwrap();
    let workspace_path = root.join("workspace");
    fs::create_dir(&workspace_path).unwrap();
    fs::set_permissions(&workspace_path, fs::Permissions::from_mode(0o700)).unwrap();
    let helper = HeldFile::open(&helper_path, FileRole::Executable).unwrap();
    let workspace = File::open(&workspace_path).unwrap();
    let writer_ready = root.join("writer-ready");
    let input = vec![b'x'; 1024 * 1024];
    let error = match execute_held_with_writer_start_control_test_only(
        &helper,
        &workspace,
        WriterControlledExecutionRequestTestOnly {
            stdin_bytes: &input,
            timeout: Duration::from_secs(2),
            stdout_cap: 64,
            stderr_cap: 64,
            argv: &[
                b"sh",
                b"-c",
                b"exec 0<&-; : > \"$1\"; exit 0",
                b"sh",
                writer_ready.as_os_str().as_bytes(),
            ],
            writer_start: WriterStartControlTestOnly {
                ready: writer_ready.clone(),
                wait_timeout: Duration::from_secs(2),
                pipe_capacity: 4_096,
                release: WriterReleaseConditionTestOnly::ReadyMarker,
            },
        },
    ) {
        Ok(_) => panic!("controlled early stdin close must fail"),
        Err(error) => error,
    };
    let observed = error.code();
    assert!(writer_ready.is_file());
    assert!(super::signal::direct_child_pids().unwrap().is_empty());
    drop(workspace);
    drop(helper);
    fs::remove_dir_all(root).unwrap();
    assert_eq!(observed, AdapterErrorCodeV0::CaptureStdin);
}

#[test]
#[serial_test::serial]
fn stdin_close_and_live_descendant_prefers_stdin() {
    let root = private_test_root("controlled-stdin-close-live-descendant");
    let helper_path = root.join("helper");
    fs::copy("/bin/sh", &helper_path).unwrap();
    fs::set_permissions(&helper_path, fs::Permissions::from_mode(0o700)).unwrap();
    let workspace_path = root.join("workspace");
    fs::create_dir(&workspace_path).unwrap();
    fs::set_permissions(&workspace_path, fs::Permissions::from_mode(0o700)).unwrap();
    let helper = HeldFile::open(&helper_path, FileRole::Executable).unwrap();
    let workspace = File::open(&workspace_path).unwrap();
    let writer_ready = root.join("writer-ready");
    let descendant_ready = root.join("descendant-ready");
    let descendant_pid = root.join("descendant-pid");
    let input = vec![b'x'; 1024 * 1024];
    let script = b"(trap '' TERM; printf '%s\\n' \"$$\" > \"$2\"; : > \"$3\"; while :; do :; done) </dev/null >/dev/null 2>&1 & while [ ! -e \"$3\" ]; do :; done; exec 0<&-; : > \"$1\"; exit 0";
    let error = match execute_held_with_writer_start_control_test_only(
        &helper,
        &workspace,
        WriterControlledExecutionRequestTestOnly {
            stdin_bytes: &input,
            timeout: Duration::from_secs(2),
            stdout_cap: 64,
            stderr_cap: 64,
            argv: &[
                b"sh",
                b"-c",
                script,
                b"sh",
                writer_ready.as_os_str().as_bytes(),
                descendant_pid.as_os_str().as_bytes(),
                descendant_ready.as_os_str().as_bytes(),
            ],
            writer_start: WriterStartControlTestOnly {
                ready: writer_ready.clone(),
                wait_timeout: Duration::from_secs(2),
                pipe_capacity: 4_096,
                release: WriterReleaseConditionTestOnly::LiveDescendantSnapshot,
            },
        },
    ) {
        Ok(_) => panic!("simultaneous stdin and live-descendant case must fail"),
        Err(error) => error,
    };
    let observed = error.code();
    assert!(writer_ready.is_file());
    assert!(descendant_ready.is_file());
    let descendant_pid = fs::read_to_string(descendant_pid).unwrap();
    assert!(!Path::new(&format!("/proc/{}", descendant_pid.trim())).exists());
    assert!(super::signal::direct_child_pids().unwrap().is_empty());
    drop(workspace);
    drop(helper);
    fs::remove_dir_all(root).unwrap();
    assert_eq!(observed, AdapterErrorCodeV0::CaptureStdin);
}

#[test]
#[serial_test::serial]
fn main_exit_with_live_descendant_after_stdin_completion_is_live_descendant() {
    let root = private_test_root("stdin-complete-live-descendant");
    let helper_path = root.join("helper");
    fs::copy("/bin/sh", &helper_path).unwrap();
    fs::set_permissions(&helper_path, fs::Permissions::from_mode(0o700)).unwrap();
    let workspace_path = root.join("workspace");
    fs::create_dir(&workspace_path).unwrap();
    fs::set_permissions(&workspace_path, fs::Permissions::from_mode(0o700)).unwrap();
    let helper = HeldFile::open(&helper_path, FileRole::Executable).unwrap();
    let workspace = File::open(&workspace_path).unwrap();
    let stdin_complete = root.join("stdin-complete");
    let descendant_ready = root.join("descendant-ready");
    let descendant_pid = root.join("descendant-pid");
    let script = b"cat >/dev/null; : > \"$1\"; (trap '' TERM; printf '%s\\n' \"$$\" > \"$3\"; : > \"$2\"; while :; do :; done) </dev/null >/dev/null 2>&1 & while [ ! -e \"$2\" ]; do :; done; exit 0";
    let error = match execute_held_test_only(
        &helper,
        &workspace,
        b"structured-input",
        Duration::from_secs(2),
        64,
        64,
        &[
            b"sh",
            b"-c",
            script,
            b"sh",
            stdin_complete.as_os_str().as_bytes(),
            descendant_ready.as_os_str().as_bytes(),
            descendant_pid.as_os_str().as_bytes(),
        ],
    ) {
        Ok(_) => panic!("live descendant must fail capture"),
        Err(error) => error,
    };
    let observed = error.code();
    assert!(stdin_complete.is_file());
    assert!(descendant_ready.is_file());
    let descendant_pid = fs::read_to_string(descendant_pid).unwrap();
    assert!(!Path::new(&format!("/proc/{}", descendant_pid.trim())).exists());
    assert!(super::signal::direct_child_pids().unwrap().is_empty());
    drop(workspace);
    drop(helper);
    fs::remove_dir_all(root).unwrap();
    assert_eq!(observed, AdapterErrorCodeV0::CaptureLiveDescendant);
}

#[test]
#[serial_test::serial]
fn held_executor_caps_timeout_termination_descendants_and_publication_fail_closed() {
    let root = std::env::temp_dir().join(format!(
        "legitimacy-process-capture-{}-{}",
        std::process::id(),
        NEXT_TEST.fetch_add(1, Ordering::Relaxed)
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
    let workspace = File::open(&workspace_path).unwrap();

    let clean = execute_held_test_only(
        &helper,
        &workspace,
        b"structured-input",
        Duration::from_secs(2),
        64,
        64,
        &[b"sh", b"-c", b"IFS= read -r value; printf '%s' \"$value\""],
    )
    .unwrap();
    assert_eq!(clean.stdout, b"structured-input");
    assert!(clean.stderr.is_empty());
    assert!(matches!(clean.termination, ObservedTermination::Exited(0)));

    let held_swap = HeldFile::open(&helper_path, FileRole::Executable).unwrap();
    fs::rename(&helper_path, root.join("held-helper")).unwrap();
    fs::copy("/bin/false", &helper_path).unwrap();
    fs::set_permissions(&helper_path, fs::Permissions::from_mode(0o700)).unwrap();
    let selected = execute_held_test_only(
        &held_swap,
        &workspace,
        b"",
        Duration::from_secs(2),
        64,
        64,
        &[b"sh", b"-c", b"printf held-fd"],
    )
    .unwrap();
    assert_eq!(selected.stdout, b"held-fd");
    assert_eq!(
        held_swap.verify().unwrap_err().code(),
        AdapterErrorCodeV0::InputChanged
    );

    for (script, expected) in [
        (
            b"while :; do printf 12345678; done".as_slice(),
            AdapterErrorCodeV0::CaptureStdoutOverflow,
        ),
        (
            b"while :; do printf 12345678 >&2; done".as_slice(),
            AdapterErrorCodeV0::CaptureStderrOverflow,
        ),
        (
            b"trap '' TERM; while :; do :; done".as_slice(),
            AdapterErrorCodeV0::CaptureTimeout,
        ),
    ] {
        let timeout = if expected == AdapterErrorCodeV0::CaptureTimeout {
            Duration::from_millis(50)
        } else {
            Duration::from_secs(2)
        };
        let error = match execute_held_test_only(
            &helper,
            &workspace,
            b"x",
            timeout,
            31,
            29,
            &[b"sh", b"-c", script],
        ) {
            Ok(_) => panic!("hostile process case must fail"),
            Err(error) => error,
        };
        assert_eq!(error.code(), expected);
    }

    let signaled = execute_held_test_only(
        &helper,
        &workspace,
        b"",
        Duration::from_secs(2),
        64,
        64,
        &[b"sh", b"-c", b"kill -TERM $$"],
    )
    .unwrap();
    assert!(matches!(
        signaled.termination,
        ObservedTermination::Signaled(15, false)
    ));

    let output = root.join("output");
    publish_output_directory(&output, [b"in", b"out", b"err", b"receipt\n"]).unwrap();
    assert_eq!(fs::read(output.join("stdout.jsonl")).unwrap(), b"out");
    for name in OUTPUTS {
        assert_eq!(
            fs::metadata(output.join(name))
                .unwrap()
                .permissions()
                .mode()
                & 0o7777,
            0o600
        );
    }
    assert_eq!(
        publish_output_directory(&output, [b"x", b"x", b"x", b"x"])
            .unwrap_err()
            .code(),
        AdapterErrorCodeV0::OutputExists
    );

    drop(workspace);
    fs::remove_dir_all(root).unwrap();
}
