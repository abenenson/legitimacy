//! Post-spawn observation, stream ownership, and typed failure selection.

use super::cleanup::{POLL_INTERVAL, RealSupervisorOperations, cleanup_process_tree};
use super::signal::{OwnedChildren, PidfdReceiveFailure};
use super::*;
use rustix::fs::{OFlags, fcntl_getfl, fcntl_setfl};
use std::io::{Read, Write};
use std::os::unix::process::ExitStatusExt;
use std::process::{Child, ExitStatus};
use std::sync::Arc;
#[cfg(test)]
use std::sync::atomic::AtomicU8;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

pub(super) struct ExecutionOutput {
    pub(super) termination: ObservedTermination,
    pub(super) stdout: Vec<u8>,
    pub(super) stderr: Vec<u8>,
}

pub(super) enum ObservedTermination {
    Exited(u8),
    Signaled(u8, bool),
}

#[cfg(test)]
#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum WriterReleaseConditionTestOnly {
    ReadyMarker,
    LiveDescendantSnapshot,
}

#[cfg(test)]
pub(super) struct WriterStartControlTestOnly {
    pub(super) ready: std::path::PathBuf,
    pub(super) wait_timeout: Duration,
    pub(super) pipe_capacity: usize,
    pub(super) release: WriterReleaseConditionTestOnly,
}

#[cfg(test)]
#[derive(Clone)]
struct WriterStartGateTestOnly {
    ready: std::path::PathBuf,
    wait_timeout: Duration,
    pipe_capacity: usize,
    release_condition: WriterReleaseConditionTestOnly,
    lifecycle: ControlledWriterLifecycleTestOnly,
}

#[cfg(test)]
#[derive(Clone, Copy, Eq, PartialEq)]
#[repr(u8)]
enum ControlledWriterStateTestOnly {
    WaitingForRelease,
    Released,
    TerminalPublished,
}

#[cfg(test)]
#[derive(Clone)]
struct ControlledWriterLifecycleTestOnly {
    state: Arc<AtomicU8>,
}

#[cfg(test)]
impl ControlledWriterLifecycleTestOnly {
    fn new() -> Self {
        Self {
            state: Arc::new(AtomicU8::new(
                ControlledWriterStateTestOnly::WaitingForRelease as u8,
            )),
        }
    }

    fn load(&self, ordering: Ordering) -> ControlledWriterStateTestOnly {
        match self.state.load(ordering) {
            value if value == ControlledWriterStateTestOnly::WaitingForRelease as u8 => {
                ControlledWriterStateTestOnly::WaitingForRelease
            }
            value if value == ControlledWriterStateTestOnly::Released as u8 => {
                ControlledWriterStateTestOnly::Released
            }
            value if value == ControlledWriterStateTestOnly::TerminalPublished as u8 => {
                ControlledWriterStateTestOnly::TerminalPublished
            }
            _ => unreachable!("controlled writer lifecycle is closed"),
        }
    }

    fn publish_release(&self) -> bool {
        self.state
            .compare_exchange(
                ControlledWriterStateTestOnly::WaitingForRelease as u8,
                ControlledWriterStateTestOnly::Released as u8,
                Ordering::Release,
                Ordering::Acquire,
            )
            .is_ok()
    }

    fn release_observed(&self) -> bool {
        matches!(
            self.load(Ordering::Acquire),
            ControlledWriterStateTestOnly::Released
                | ControlledWriterStateTestOnly::TerminalPublished
        )
    }

    fn publish_terminal(&self) {
        let transition = self.state.compare_exchange(
            ControlledWriterStateTestOnly::Released as u8,
            ControlledWriterStateTestOnly::TerminalPublished as u8,
            Ordering::Release,
            Ordering::Acquire,
        );
        debug_assert!(transition.is_ok());
    }

    fn terminal_published(&self) -> bool {
        self.load(Ordering::Acquire) == ControlledWriterStateTestOnly::TerminalPublished
    }
}

#[cfg(test)]
impl WriterStartGateTestOnly {
    fn new(control: WriterStartControlTestOnly) -> Self {
        Self {
            ready: control.ready,
            wait_timeout: control.wait_timeout,
            pipe_capacity: control.pipe_capacity,
            release_condition: control.release,
            lifecycle: ControlledWriterLifecycleTestOnly::new(),
        }
    }

    fn await_release(&self) -> bool {
        let deadline = Instant::now() + self.wait_timeout;
        loop {
            let released = match self.release_condition {
                WriterReleaseConditionTestOnly::ReadyMarker => self.ready.is_file(),
                WriterReleaseConditionTestOnly::LiveDescendantSnapshot => {
                    self.lifecycle.release_observed()
                }
            };
            if released {
                return true;
            }
            if Instant::now() >= deadline {
                return false;
            }
            thread::yield_now();
        }
    }

    fn release_after_live_descendant_snapshot(&self) -> bool {
        if self.release_condition == WriterReleaseConditionTestOnly::LiveDescendantSnapshot
            && self.ready.is_file()
        {
            return self.lifecycle.publish_release();
        }
        false
    }

    fn publish_terminal_after_write_stream(&self) {
        if self.release_condition == WriterReleaseConditionTestOnly::LiveDescendantSnapshot {
            self.lifecycle.publish_terminal();
        }
    }

    fn await_terminal_publication(&self) -> bool {
        debug_assert!(
            self.release_condition == WriterReleaseConditionTestOnly::LiveDescendantSnapshot
        );
        let deadline = Instant::now() + self.wait_timeout;
        loop {
            if self.lifecycle.terminal_published() {
                return true;
            }
            if Instant::now() >= deadline {
                return false;
            }
            thread::yield_now();
        }
    }
}

impl ObservedTermination {
    fn from_status(status: ExitStatus) -> AdapterResultV0<Self> {
        if let Some(code) = status.code() {
            return u8::try_from(code)
                .map(Self::Exited)
                .map_err(|_| error(AdapterErrorCodeV0::IllegalTermination));
        }
        status
            .signal()
            .and_then(|signal| u8::try_from(signal).ok())
            .map(|signal| Self::Signaled(signal, status.core_dumped()))
            .ok_or_else(|| error(AdapterErrorCodeV0::IllegalTermination))
    }

    pub(super) fn into_receipt(self) -> AdapterResultV0<ProcessTerminationV0> {
        match self {
            Self::Exited(code) if code <= 125 => Ok(ProcessTerminationV0::Exited { code }),
            Self::Signaled(signal, core_dumped) if (1..=64).contains(&signal) => {
                Ok(ProcessTerminationV0::Signaled {
                    signal,
                    core_dumped,
                })
            }
            _ => Err(error(AdapterErrorCodeV0::IllegalTermination)),
        }
    }
}

pub(super) fn contain_pidfd_receipt_failure(
    child: &mut Child,
    receipt_failure: PidfdReceiveFailure,
) -> AdapterResultV0<ExecutionOutput> {
    let recovered = receipt_failure
        .recovered
        .ok_or_else(|| error(AdapterErrorCodeV0::CaptureCleanup))?;
    let mut owned = OwnedChildren::new(child.id(), recovered);
    let mut status = None;
    let mut operations = RealSupervisorOperations;
    cleanup_process_tree(&mut operations, child, &mut status, &mut owned)?;
    Err(error(AdapterErrorCodeV0::CaptureSpawn))
}

enum WorkerCompletion<T> {
    Complete(T),
    Cancelled,
    Failed,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
enum PrimaryCaptureFailure {
    StdoutOverflow,
    StderrOverflow,
    Stdin,
    StreamState,
    Timeout,
    LiveDescendant,
}

impl PrimaryCaptureFailure {
    const PRECEDENCE: [Self; 6] = [
        Self::StdoutOverflow,
        Self::StderrOverflow,
        Self::Stdin,
        Self::StreamState,
        Self::Timeout,
        Self::LiveDescendant,
    ];

    const fn code(self) -> AdapterErrorCodeV0 {
        match self {
            Self::StdoutOverflow => AdapterErrorCodeV0::CaptureStdoutOverflow,
            Self::StderrOverflow => AdapterErrorCodeV0::CaptureStderrOverflow,
            Self::Stdin => AdapterErrorCodeV0::CaptureStdin,
            Self::StreamState => AdapterErrorCodeV0::StreamState,
            Self::Timeout => AdapterErrorCodeV0::CaptureTimeout,
            Self::LiveDescendant => AdapterErrorCodeV0::CaptureLiveDescendant,
        }
    }
}

#[derive(Clone, Copy, Default)]
struct PrimaryCaptureFailures(u8);

impl PrimaryCaptureFailures {
    fn insert(&mut self, failure: PrimaryCaptureFailure) {
        self.0 |= 1 << (failure as u8);
    }

    fn selected(self) -> Option<PrimaryCaptureFailure> {
        PrimaryCaptureFailure::PRECEDENCE
            .into_iter()
            .find(|failure| self.0 & (1 << (*failure as u8)) != 0)
    }

    fn union(&mut self, other: Self) {
        self.0 |= other.0;
    }
}

#[derive(Debug, Eq, PartialEq)]
enum SupervisionDecision {
    CleanupUncertain,
    Primary(PrimaryCaptureFailure),
    Success,
    Continue,
}

fn select_supervision_decision(
    primary: PrimaryCaptureFailures,
    cleanup_uncertain: bool,
    success_ready: bool,
) -> SupervisionDecision {
    if cleanup_uncertain {
        SupervisionDecision::CleanupUncertain
    } else if let Some(primary) = primary.selected() {
        SupervisionDecision::Primary(primary)
    } else if success_ready {
        SupervisionDecision::Success
    } else {
        SupervisionDecision::Continue
    }
}

struct WorkerHandles {
    cancel: Arc<AtomicBool>,
    writer: Option<JoinHandle<WorkerCompletion<()>>>,
    stdout: Option<JoinHandle<WorkerCompletion<Vec<u8>>>>,
    stderr: Option<JoinHandle<WorkerCompletion<Vec<u8>>>>,
}

#[derive(Clone)]
struct WorkerFailureFacts {
    writer_failed: Arc<AtomicBool>,
    stdout_overflow: Arc<AtomicBool>,
    stderr_overflow: Arc<AtomicBool>,
    stdout_failed: Arc<AtomicBool>,
    stderr_failed: Arc<AtomicBool>,
}

impl WorkerFailureFacts {
    fn new() -> Self {
        Self {
            writer_failed: Arc::new(AtomicBool::new(false)),
            stdout_overflow: Arc::new(AtomicBool::new(false)),
            stderr_overflow: Arc::new(AtomicBool::new(false)),
            stdout_failed: Arc::new(AtomicBool::new(false)),
            stderr_failed: Arc::new(AtomicBool::new(false)),
        }
    }

    fn snapshot(&self) -> PrimaryCaptureFailures {
        let mut primary = PrimaryCaptureFailures::default();
        if self.stdout_overflow.load(Ordering::Acquire) {
            primary.insert(PrimaryCaptureFailure::StdoutOverflow);
        }
        if self.stderr_overflow.load(Ordering::Acquire) {
            primary.insert(PrimaryCaptureFailure::StderrOverflow);
        }
        if self.writer_failed.load(Ordering::Acquire) {
            primary.insert(PrimaryCaptureFailure::Stdin);
        }
        if self.stdout_failed.load(Ordering::Acquire) || self.stderr_failed.load(Ordering::Acquire)
        {
            primary.insert(PrimaryCaptureFailure::StreamState);
        }
        primary
    }
}

struct JoinedWorkers {
    writer: Option<WorkerCompletion<()>>,
    stdout: Option<WorkerCompletion<Vec<u8>>>,
    stderr: Option<WorkerCompletion<Vec<u8>>>,
    join_uncertain: bool,
}

enum CleanupJoinOutcome {
    Closed(JoinedWorkers),
    Uncertain,
}

impl WorkerHandles {
    fn new() -> Self {
        Self {
            cancel: Arc::new(AtomicBool::new(false)),
            writer: None,
            stdout: None,
            stderr: None,
        }
    }

    fn cancel_and_join(mut self) -> JoinedWorkers {
        self.cancel.store(true, Ordering::Release);
        let (writer, writer_panic) = join_one(self.writer.take());
        let (stdout, stdout_panic) = join_one(self.stdout.take());
        let (stderr, stderr_panic) = join_one(self.stderr.take());
        JoinedWorkers {
            writer,
            stdout,
            stderr,
            join_uncertain: writer_panic || stdout_panic || stderr_panic,
        }
    }

    fn join(mut self) -> JoinedWorkers {
        let (writer, writer_panic) = join_one(self.writer.take());
        let (stdout, stdout_panic) = join_one(self.stdout.take());
        let (stderr, stderr_panic) = join_one(self.stderr.take());
        JoinedWorkers {
            writer,
            stdout,
            stderr,
            join_uncertain: writer_panic || stdout_panic || stderr_panic,
        }
    }
}

fn join_one<T>(
    handle: Option<JoinHandle<WorkerCompletion<T>>>,
) -> (Option<WorkerCompletion<T>>, bool) {
    match handle {
        Some(handle) => match handle.join() {
            Ok(value) => (Some(value), false),
            Err(_) => (None, true),
        },
        None => (None, false),
    }
}

#[cfg(test)]
pub(super) fn pipe_join_fault_control() -> (usize, bool, Duration) {
    let joined_count = Arc::new(std::sync::atomic::AtomicUsize::new(0));
    let mut workers = WorkerHandles::new();
    let writer_count = Arc::clone(&joined_count);
    workers.writer = Some(thread::spawn(move || {
        writer_count.fetch_add(1, Ordering::AcqRel);
        WorkerCompletion::Complete(())
    }));
    let stdout_count = Arc::clone(&joined_count);
    workers.stdout = Some(thread::spawn(move || -> WorkerCompletion<Vec<u8>> {
        stdout_count.fetch_add(1, Ordering::AcqRel);
        panic!("injected pipe worker completion failure")
    }));
    let stderr_count = Arc::clone(&joined_count);
    workers.stderr = Some(thread::spawn(move || {
        stderr_count.fetch_add(1, Ordering::AcqRel);
        WorkerCompletion::Complete(Vec::new())
    }));
    let started = Instant::now();
    let joined = workers.cancel_and_join();
    (
        joined_count.load(Ordering::Acquire),
        joined.join_uncertain,
        started.elapsed(),
    )
}

#[cfg(test)]
#[derive(Clone, Copy)]
pub(super) enum PrimaryPublicationOrderingTestOnly {
    BeforeCleanup,
    AfterCancellation,
}

#[cfg(test)]
pub(super) fn closed_failure_observation_control(
    ordering: PrimaryPublicationOrderingTestOnly,
    cleanup_uncertain: bool,
) -> AdapterErrorCodeV0 {
    let worker_failures = WorkerFailureFacts::new();
    worker_failures
        .stderr_overflow
        .store(true, Ordering::Release);
    let observed = worker_failures.snapshot();
    let mut workers = WorkerHandles::new();
    match ordering {
        PrimaryPublicationOrderingTestOnly::BeforeCleanup => worker_failures
            .stdout_overflow
            .store(true, Ordering::Release),
        PrimaryPublicationOrderingTestOnly::AfterCancellation => {
            let cancel = Arc::clone(&workers.cancel);
            let stdout_overflow = Arc::clone(&worker_failures.stdout_overflow);
            workers.stdout = Some(thread::spawn(move || {
                while !cancel.load(Ordering::Acquire) {
                    thread::yield_now();
                }
                stdout_overflow.store(true, Ordering::Release);
                WorkerCompletion::Cancelled
            }));
        }
    }
    let joined = workers.cancel_and_join();
    if cleanup_uncertain || joined.join_uncertain {
        return AdapterErrorCodeV0::CaptureCleanup;
    }
    close_worker_failure_observation(observed, &worker_failures, &joined, true)
        .selected()
        .expect("stderr overflow seeds one primary failure")
        .code()
}

pub(super) fn supervise_spawned_child(
    main_pidfd: std::os::fd::OwnedFd,
    child: &mut Child,
    stdin_bytes: &[u8],
    timeout: Duration,
    stdout_cap: usize,
    stderr_cap: usize,
    #[cfg(test)] writer_start: Option<WriterStartControlTestOnly>,
) -> AdapterResultV0<ExecutionOutput> {
    #[cfg(test)]
    let writer_start = writer_start.map(WriterStartGateTestOnly::new);
    let mut workers = WorkerHandles::new();
    let mut status = None;
    let mut owned = OwnedChildren::new(child.id(), main_pidfd);
    let Some(child_stdin) = child.stdin.take() else {
        return cleanup_spawn_and_fail(child, status, &mut owned, workers);
    };
    let Some(child_stdout) = child.stdout.take() else {
        return cleanup_spawn_and_fail(child, status, &mut owned, workers);
    };
    let Some(child_stderr) = child.stderr.take() else {
        return cleanup_spawn_and_fail(child, status, &mut owned, workers);
    };
    #[cfg(test)]
    if let Some(control) = &writer_start {
        let capacity = match rustix::pipe::fcntl_setpipe_size(&child_stdin, control.pipe_capacity) {
            Ok(capacity) if stdin_bytes.len() > capacity => capacity,
            Ok(_) | Err(_) => return cleanup_spawn_and_fail(child, status, &mut owned, workers),
        };
        debug_assert!(stdin_bytes.len() > capacity);
    }
    for descriptor in [
        &child_stdin as &dyn std::os::fd::AsFd,
        &child_stdout,
        &child_stderr,
    ] {
        if make_nonblocking(descriptor).is_err() {
            return cleanup_spawn_and_fail(child, status, &mut owned, workers);
        }
    }

    let worker_failures = WorkerFailureFacts::new();
    let input = stdin_bytes.to_vec();
    let writer_cancel = Arc::clone(&workers.cancel);
    let writer_flag = Arc::clone(&worker_failures.writer_failed);
    #[cfg(test)]
    let writer_gate = writer_start.clone();
    workers.writer = match thread::Builder::new().spawn(move || {
        #[cfg(test)]
        if writer_gate
            .as_ref()
            .is_some_and(|control| !control.await_release())
        {
            writer_flag.store(true, Ordering::Release);
            return WorkerCompletion::Failed;
        }
        let completion = write_stream(child_stdin, &input, &writer_cancel, &writer_flag);
        #[cfg(test)]
        if let Some(control) = &writer_gate {
            control.publish_terminal_after_write_stream();
        }
        completion
    }) {
        Ok(handle) => Some(handle),
        Err(_) => {
            return cleanup_spawn_and_fail(child, status, &mut owned, workers);
        }
    };
    let stdout_cancel = Arc::clone(&workers.cancel);
    let stdout_overflow_flag = Arc::clone(&worker_failures.stdout_overflow);
    let stdout_failed_flag = Arc::clone(&worker_failures.stdout_failed);
    workers.stdout = match thread::Builder::new().spawn(move || {
        read_stream(
            child_stdout,
            stdout_cap,
            &stdout_cancel,
            &stdout_overflow_flag,
            &stdout_failed_flag,
        )
    }) {
        Ok(handle) => Some(handle),
        Err(_) => {
            return cleanup_spawn_and_fail(child, status, &mut owned, workers);
        }
    };
    let stderr_cancel = Arc::clone(&workers.cancel);
    let stderr_overflow_flag = Arc::clone(&worker_failures.stderr_overflow);
    let stderr_failed_flag = Arc::clone(&worker_failures.stderr_failed);
    workers.stderr = match thread::Builder::new().spawn(move || {
        read_stream(
            child_stderr,
            stderr_cap,
            &stderr_cancel,
            &stderr_overflow_flag,
            &stderr_failed_flag,
        )
    }) {
        Ok(handle) => Some(handle),
        Err(_) => {
            return cleanup_spawn_and_fail(child, status, &mut owned, workers);
        }
    };

    let deadline = Instant::now() + timeout;
    let mut observed_primary = PrimaryCaptureFailures::default();
    let failure = loop {
        let mut cleanup_uncertain = owned.observe_direct().is_err();
        if status.is_none() && !cleanup_uncertain {
            match child.try_wait() {
                Ok(observed) => {
                    status = observed;
                    if status.is_some() {
                        owned.main_reaped();
                    }
                }
                Err(_) => cleanup_uncertain = true,
            }
        }
        observed_primary.union(worker_failures.snapshot());
        if Instant::now() >= deadline {
            observed_primary.insert(PrimaryCaptureFailure::Timeout);
        }
        let mut success_ready = false;
        #[cfg(test)]
        let mut live_descendant = false;
        if status.is_some() && !cleanup_uncertain {
            if owned.reap_adopted().is_err() {
                cleanup_uncertain = true;
            } else {
                match owned.fresh_absence() {
                    Ok(true)
                        if workers.writer.as_ref().is_some_and(JoinHandle::is_finished)
                            && workers.stdout.as_ref().is_some_and(JoinHandle::is_finished)
                            && workers.stderr.as_ref().is_some_and(JoinHandle::is_finished) =>
                    {
                        success_ready = true;
                    }
                    Ok(false) => {
                        observed_primary.insert(PrimaryCaptureFailure::LiveDescendant);
                        #[cfg(test)]
                        {
                            live_descendant = true;
                        }
                    }
                    Ok(true) => {}
                    Err(_) => cleanup_uncertain = true,
                }
            }
        }
        #[cfg(test)]
        if live_descendant
            && let Some(control) = &writer_start
            && control.release_after_live_descendant_snapshot()
        {
            if control.await_terminal_publication() {
                continue;
            }
            cleanup_uncertain = true;
        }
        match select_supervision_decision(observed_primary, cleanup_uncertain, success_ready) {
            SupervisionDecision::CleanupUncertain => {
                break Some(SupervisionFailure::CleanupUncertain);
            }
            SupervisionDecision::Primary(_) => {
                break Some(SupervisionFailure::Primary);
            }
            SupervisionDecision::Success => break None,
            SupervisionDecision::Continue => thread::sleep(POLL_INTERVAL),
        }
    };

    if let Some(failure) = failure {
        return match failure {
            SupervisionFailure::CleanupUncertain => {
                cleanup_uncertain_and_fail(child, status, &mut owned, workers)
            }
            SupervisionFailure::Primary => cleanup_and_fail(
                child,
                status,
                &mut owned,
                workers,
                observed_primary,
                &worker_failures,
            ),
        };
    }
    let joined = workers.join();
    if joined.join_uncertain {
        return Err(error(AdapterErrorCodeV0::CaptureCleanup));
    }
    let final_primary = close_worker_failure_observation(
        PrimaryCaptureFailures::default(),
        &worker_failures,
        &joined,
        false,
    );
    let status = status.ok_or_else(|| error(AdapterErrorCodeV0::CaptureCleanup))?;
    owned.reap_adopted()?;
    if !owned.fresh_absence()? {
        return Err(error(AdapterErrorCodeV0::CaptureCleanup));
    }
    if let Some(primary) = final_primary.selected() {
        return Err(error(primary.code()));
    }
    let Some(WorkerCompletion::Complete(stdout)) = joined.stdout else {
        unreachable!("stream failure returned through typed primary selection");
    };
    let Some(WorkerCompletion::Complete(stderr)) = joined.stderr else {
        unreachable!("stream failure returned through typed primary selection");
    };
    Ok(ExecutionOutput {
        termination: ObservedTermination::from_status(status)?,
        stdout,
        stderr,
    })
}

fn make_nonblocking(descriptor: &dyn std::os::fd::AsFd) -> AdapterResultV0<()> {
    let flags = fcntl_getfl(descriptor).map_err(|_| error(AdapterErrorCodeV0::CaptureSpawn))?;
    fcntl_setfl(descriptor, flags | OFlags::NONBLOCK)
        .map_err(|_| error(AdapterErrorCodeV0::CaptureSpawn))
}

fn write_stream(
    mut stream: impl Write,
    input: &[u8],
    cancel: &AtomicBool,
    failed: &AtomicBool,
) -> WorkerCompletion<()> {
    let mut offset = 0;
    while offset < input.len() {
        if cancel.load(Ordering::Acquire) {
            return WorkerCompletion::Cancelled;
        }
        match stream.write(&input[offset..]) {
            Ok(0) => {
                failed.store(true, Ordering::Release);
                return WorkerCompletion::Failed;
            }
            Ok(count) => offset += count,
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                thread::sleep(POLL_INTERVAL);
            }
            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => {}
            Err(_) => {
                failed.store(true, Ordering::Release);
                return WorkerCompletion::Failed;
            }
        }
    }
    WorkerCompletion::Complete(())
}

fn read_stream(
    mut stream: impl Read,
    cap: usize,
    cancel: &AtomicBool,
    overflow: &AtomicBool,
    failed: &AtomicBool,
) -> WorkerCompletion<Vec<u8>> {
    let mut retained = Vec::with_capacity(cap.min(READ_CHUNK));
    let mut buffer = [0_u8; READ_CHUNK];
    loop {
        if cancel.load(Ordering::Acquire) {
            return WorkerCompletion::Cancelled;
        }
        match stream.read(&mut buffer) {
            Ok(0) => return WorkerCompletion::Complete(retained),
            Ok(count) => {
                let remaining = cap.saturating_sub(retained.len());
                retained.extend_from_slice(&buffer[..count.min(remaining)]);
                if count > remaining {
                    overflow.store(true, Ordering::Release);
                }
            }
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                thread::sleep(POLL_INTERVAL);
            }
            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => {}
            Err(_) => {
                failed.store(true, Ordering::Release);
                return WorkerCompletion::Failed;
            }
        }
    }
}

enum SupervisionFailure {
    CleanupUncertain,
    Primary,
}

fn cleanup_and_join(
    child: &mut Child,
    mut status: Option<ExitStatus>,
    owned: &mut OwnedChildren,
    workers: WorkerHandles,
) -> CleanupJoinOutcome {
    let mut operations = RealSupervisorOperations;
    let cleanup = cleanup_process_tree(&mut operations, child, &mut status, owned);
    let joined = workers.cancel_and_join();
    if cleanup.is_ok() && !joined.join_uncertain {
        CleanupJoinOutcome::Closed(joined)
    } else {
        CleanupJoinOutcome::Uncertain
    }
}

fn cleanup_and_fail(
    child: &mut Child,
    status: Option<ExitStatus>,
    owned: &mut OwnedChildren,
    workers: WorkerHandles,
    observed_primary: PrimaryCaptureFailures,
    worker_failures: &WorkerFailureFacts,
) -> AdapterResultV0<ExecutionOutput> {
    match cleanup_and_join(child, status, owned, workers) {
        CleanupJoinOutcome::Closed(joined) => {
            let closed_primary =
                close_worker_failure_observation(observed_primary, worker_failures, &joined, true);
            let primary = closed_primary
                .selected()
                .expect("a primary failure triggered cleanup");
            Err(error(primary.code()))
        }
        CleanupJoinOutcome::Uncertain => Err(error(AdapterErrorCodeV0::CaptureCleanup)),
    }
}

fn close_worker_failure_observation(
    mut observed: PrimaryCaptureFailures,
    worker_failures: &WorkerFailureFacts,
    joined: &JoinedWorkers,
    cancellation_expected: bool,
) -> PrimaryCaptureFailures {
    observed.union(worker_failures.snapshot());
    match &joined.writer {
        Some(WorkerCompletion::Failed) => observed.insert(PrimaryCaptureFailure::Stdin),
        Some(WorkerCompletion::Cancelled) if !cancellation_expected => {
            observed.insert(PrimaryCaptureFailure::Stdin);
        }
        _ => {}
    }
    for completion in [&joined.stdout, &joined.stderr] {
        match completion {
            Some(WorkerCompletion::Failed) => {
                observed.insert(PrimaryCaptureFailure::StreamState);
            }
            Some(WorkerCompletion::Cancelled) if !cancellation_expected => {
                observed.insert(PrimaryCaptureFailure::StreamState);
            }
            _ => {}
        }
    }
    observed
}

fn cleanup_uncertain_and_fail(
    child: &mut Child,
    status: Option<ExitStatus>,
    owned: &mut OwnedChildren,
    workers: WorkerHandles,
) -> AdapterResultV0<ExecutionOutput> {
    let _cleanup_outcome = cleanup_and_join(child, status, owned, workers);
    Err(error(AdapterErrorCodeV0::CaptureCleanup))
}

fn cleanup_spawn_and_fail(
    child: &mut Child,
    status: Option<ExitStatus>,
    owned: &mut OwnedChildren,
    workers: WorkerHandles,
) -> AdapterResultV0<ExecutionOutput> {
    match cleanup_and_join(child, status, owned, workers) {
        CleanupJoinOutcome::Closed(_) => Err(error(AdapterErrorCodeV0::CaptureSpawn)),
        CleanupJoinOutcome::Uncertain => Err(error(AdapterErrorCodeV0::CaptureCleanup)),
    }
}

#[cfg(test)]
mod precedence_tests {
    use super::*;

    #[test]
    fn selector_covers_every_primary_pair_in_one_closed_order() {
        for (higher_index, higher) in PrimaryCaptureFailure::PRECEDENCE.iter().enumerate() {
            let mut singleton = PrimaryCaptureFailures::default();
            singleton.insert(*higher);
            assert_eq!(
                select_supervision_decision(singleton, false, false),
                SupervisionDecision::Primary(*higher)
            );
            assert_eq!(
                higher.code().as_str(),
                match higher {
                    PrimaryCaptureFailure::StdoutOverflow => "capture-stdout-overflow",
                    PrimaryCaptureFailure::StderrOverflow => "capture-stderr-overflow",
                    PrimaryCaptureFailure::Stdin => "capture-stdin",
                    PrimaryCaptureFailure::StreamState => "stream-state",
                    PrimaryCaptureFailure::Timeout => "capture-timeout",
                    PrimaryCaptureFailure::LiveDescendant => "capture-live-descendant",
                }
            );
            for lower in &PrimaryCaptureFailure::PRECEDENCE[higher_index + 1..] {
                let mut pair = PrimaryCaptureFailures::default();
                pair.insert(*lower);
                pair.insert(*higher);
                assert_eq!(
                    select_supervision_decision(pair, false, false),
                    SupervisionDecision::Primary(*higher),
                    "{higher:?} must precede {lower:?}"
                );
            }
        }
    }

    #[test]
    fn cleanup_uncertainty_overrides_every_primary() {
        for primary in PrimaryCaptureFailure::PRECEDENCE {
            let mut failures = PrimaryCaptureFailures::default();
            failures.insert(primary);
            assert_eq!(
                select_supervision_decision(failures, true, true),
                SupervisionDecision::CleanupUncertain
            );
        }
    }
}
