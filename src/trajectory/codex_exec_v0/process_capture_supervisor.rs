//! Bounded, single-purpose Linux child spawn owner for process capture.

use super::signal::{
    ChildSignalBoundary, PidfdReceiveFailure, acknowledge_pidfd_receipt, await_pidfd_receipt_ack,
    direct_child_pids, pidfd_channel, receive_pidfd, send_self_pidfd,
};
#[cfg(test)]
use super::signal::{receive_pidfd_permanent_error_test_only, send_pidfd_packet_without_handle};
#[cfg(test)]
use super::supervision::WriterStartControlTestOnly;
use super::supervision::{ExecutionOutput, contain_pidfd_receipt_failure, supervise_spawned_child};
use super::*;
use rustix::process::Pid;
use std::os::unix::process::CommandExt;
use std::process::{Command, Stdio};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;
#[cfg(test)]
use std::time::Instant;

struct ExecutionRequest<'a> {
    stdin_bytes: &'a [u8],
    timeout: Duration,
    stdout_cap: usize,
    stderr_cap: usize,
    argv: &'a [&'a [u8]],
    #[cfg(test)]
    writer_start: Option<WriterStartControlTestOnly>,
}

enum PreExecReceiptOwnership {
    None,
    Accepted(std::os::fd::OwnedFd),
    Rejected(std::os::fd::OwnedFd),
}

pub(super) fn require_single_purpose_process() -> AdapterResultV0<()> {
    let task_directory =
        File::open("/proc/self/task").map_err(|_| error(AdapterErrorCodeV0::CaptureSpawn))?;
    let mut tasks =
        Dir::read_from(&task_directory).map_err(|_| error(AdapterErrorCodeV0::CaptureSpawn))?;
    let mut task_count = 0_u8;
    while let Some(entry) = tasks.read() {
        let entry = entry.map_err(|_| error(AdapterErrorCodeV0::CaptureSpawn))?;
        if matches!(entry.file_name().to_bytes(), b"." | b"..") {
            continue;
        }
        if entry.file_name().to_bytes().iter().all(u8::is_ascii_digit) {
            task_count = task_count.saturating_add(1);
        }
    }
    if task_count != 1 || !direct_child_pids()?.is_empty() {
        return Err(error(AdapterErrorCodeV0::CaptureSpawn));
    }
    Ok(())
}

pub(super) fn execute_held(
    executable: &HeldFile,
    workspace: &File,
    stdin_bytes: &[u8],
    timeout: Duration,
    stdout_cap: usize,
    stderr_cap: usize,
    argv: &[&[u8]],
) -> AdapterResultV0<ExecutionOutput> {
    require_single_purpose_process()?;
    execute_held_with_boundary(
        executable,
        workspace,
        ExecutionRequest {
            stdin_bytes,
            timeout,
            stdout_cap,
            stderr_cap,
            argv,
            #[cfg(test)]
            writer_start: None,
        },
    )
}

fn execute_held_with_boundary(
    executable: &HeldFile,
    workspace: &File,
    request: ExecutionRequest<'_>,
) -> AdapterResultV0<ExecutionOutput> {
    execute_held_with_boundary_control(
        executable,
        workspace,
        request,
        PidfdReceiptControl::Ordinary,
    )
}

fn execute_held_with_boundary_control(
    executable: &HeldFile,
    workspace: &File,
    request: ExecutionRequest<'_>,
    receipt_control: PidfdReceiptControl,
) -> AdapterResultV0<ExecutionOutput> {
    let signal_boundary = ChildSignalBoundary::enter()?;
    let previous_subreaper =
        rustix::process::child_subreaper().map_err(|_| error(AdapterErrorCodeV0::CaptureSpawn))?;
    let true_pid = Pid::from_raw(1).ok_or_else(|| error(AdapterErrorCodeV0::CaptureSpawn))?;
    rustix::process::set_child_subreaper(Some(true_pid))
        .map_err(|_| error(AdapterErrorCodeV0::CaptureSpawn))?;
    let outcome = execute_held_inner(
        executable,
        workspace,
        request,
        signal_boundary.child_state(),
        receipt_control,
    );
    let restored = rustix::process::set_child_subreaper(previous_subreaper)
        .map_err(|_| error(AdapterErrorCodeV0::CaptureCleanup));
    let signal_restored = signal_boundary.restore();
    match (outcome, restored, signal_restored) {
        (_, Err(cleanup), _) | (_, _, Err(cleanup)) => Err(cleanup),
        (outcome, Ok(()), Ok(())) => outcome,
    }
}

#[cfg(test)]
pub(super) fn execute_held_test_only(
    executable: &HeldFile,
    workspace: &File,
    stdin_bytes: &[u8],
    timeout: Duration,
    stdout_cap: usize,
    stderr_cap: usize,
    argv: &[&[u8]],
) -> AdapterResultV0<ExecutionOutput> {
    execute_held_with_boundary(
        executable,
        workspace,
        ExecutionRequest {
            stdin_bytes,
            timeout,
            stdout_cap,
            stderr_cap,
            argv,
            writer_start: None,
        },
    )
}

#[cfg(test)]
pub(super) struct WriterControlledExecutionRequestTestOnly<'a> {
    pub(super) stdin_bytes: &'a [u8],
    pub(super) timeout: Duration,
    pub(super) stdout_cap: usize,
    pub(super) stderr_cap: usize,
    pub(super) argv: &'a [&'a [u8]],
    pub(super) writer_start: WriterStartControlTestOnly,
}

#[cfg(test)]
pub(super) fn execute_held_with_writer_start_control_test_only(
    executable: &HeldFile,
    workspace: &File,
    request: WriterControlledExecutionRequestTestOnly<'_>,
) -> AdapterResultV0<ExecutionOutput> {
    execute_held_with_boundary(
        executable,
        workspace,
        ExecutionRequest {
            stdin_bytes: request.stdin_bytes,
            timeout: request.timeout,
            stdout_cap: request.stdout_cap,
            stderr_cap: request.stderr_cap,
            argv: request.argv,
            writer_start: Some(request.writer_start),
        },
    )
}

#[cfg(test)]
pub(super) enum PidfdReceiptFaultTestOnly {
    FailureAfterOwnedReceipt,
    PermanentReceiveErrorBeforeExec,
    HandlelessPacketBeforeExec,
    FallbackAcquisitionFailureBeforeExec,
}

#[cfg(test)]
pub(super) struct PidfdReceiptFaultRequestTestOnly<'a> {
    pub(super) argv: &'a [&'a [u8]],
    pub(super) ready: std::path::PathBuf,
    pub(super) fault: PidfdReceiptFaultTestOnly,
}

#[cfg(test)]
pub(super) fn execute_held_pidfd_receipt_fault_test_only(
    executable: &HeldFile,
    workspace: &File,
    stdin_bytes: &[u8],
    timeout: Duration,
    stdout_cap: usize,
    stderr_cap: usize,
    fault_request: PidfdReceiptFaultRequestTestOnly<'_>,
) -> AdapterResultV0<ExecutionOutput> {
    let receipt_control = match fault_request.fault {
        PidfdReceiptFaultTestOnly::FailureAfterOwnedReceipt => {
            PidfdReceiptControl::FailAfterOwnedReceipt(fault_request.ready)
        }
        PidfdReceiptFaultTestOnly::PermanentReceiveErrorBeforeExec => {
            PidfdReceiptControl::PermanentReceiveErrorBeforeExec
        }
        PidfdReceiptFaultTestOnly::HandlelessPacketBeforeExec => {
            PidfdReceiptControl::HandlelessPacketBeforeExec
        }
        PidfdReceiptFaultTestOnly::FallbackAcquisitionFailureBeforeExec => {
            PidfdReceiptControl::FallbackAcquisitionFailureBeforeExec
        }
    };
    execute_held_with_boundary_control(
        executable,
        workspace,
        ExecutionRequest {
            stdin_bytes,
            timeout,
            stdout_cap,
            stderr_cap,
            argv: fault_request.argv,
            writer_start: None,
        },
        receipt_control,
    )
}

enum PidfdReceiptControl {
    Ordinary,
    #[cfg(test)]
    FailAfterOwnedReceipt(std::path::PathBuf),
    #[cfg(test)]
    PermanentReceiveErrorBeforeExec,
    #[cfg(test)]
    HandlelessPacketBeforeExec,
    #[cfg(test)]
    FallbackAcquisitionFailureBeforeExec,
}

impl PidfdReceiptControl {
    #[cfg(test)]
    fn send_handleless_before_exec(&self) -> bool {
        matches!(self, Self::HandlelessPacketBeforeExec)
    }

    #[cfg(test)]
    fn inject_permanent_receive_error(&self) -> bool {
        matches!(
            self,
            Self::PermanentReceiveErrorBeforeExec | Self::FallbackAcquisitionFailureBeforeExec
        )
    }

    #[cfg(not(test))]
    fn inject_permanent_receive_error(&self) -> bool {
        false
    }

    #[cfg(test)]
    fn wait_for_ready(ready: &std::path::Path) -> bool {
        let deadline = Instant::now() + Duration::from_secs(2);
        while !ready.exists() && Instant::now() < deadline {
            thread::yield_now();
        }
        ready.exists()
    }

    fn finish_after_spawn(
        self,
        received: std::os::fd::OwnedFd,
    ) -> Result<std::os::fd::OwnedFd, PidfdReceiveFailure> {
        #[cfg(test)]
        match self {
            Self::FailAfterOwnedReceipt(ready) => {
                let _ = Self::wait_for_ready(&ready);
                return Err(PidfdReceiveFailure {
                    recovered: Some(received),
                });
            }
            Self::PermanentReceiveErrorBeforeExec
            | Self::HandlelessPacketBeforeExec
            | Self::FallbackAcquisitionFailureBeforeExec => {}
            Self::Ordinary => {}
        }
        Ok(received)
    }
}

fn execute_held_inner(
    executable: &HeldFile,
    workspace: &File,
    request: ExecutionRequest<'_>,
    child_signal_state: super::signal::ChildSignalState,
    receipt_control: PidfdReceiptControl,
) -> AdapterResultV0<ExecutionOutput> {
    if request.timeout.is_zero() {
        return Err(error(AdapterErrorCodeV0::CaptureTimeout));
    }
    let executable_fd = executable
        .file
        .try_clone()
        .map_err(|_| error(AdapterErrorCodeV0::CaptureSpawn))?;
    let workspace_fd = workspace
        .try_clone()
        .map_err(|_| error(AdapterErrorCodeV0::CaptureSpawn))?;
    let argv = c_strings(request.argv)?;
    let argv_pointers = argv
        .iter()
        .map(|value| value.as_ptr() as usize)
        .chain(std::iter::once(0))
        .collect::<Vec<_>>();
    let environment = capture_environment()?;
    let environment_pointers = environment
        .iter()
        .map(|value| value.as_ptr() as usize)
        .chain(std::iter::once(0))
        .collect::<Vec<_>>();
    let (pidfd_receiver, pidfd_sender) = pidfd_channel()?;
    let pidfd_receiver_raw = pidfd_receiver.as_raw_fd();
    #[cfg(test)]
    let send_handleless_before_exec = receipt_control.send_handleless_before_exec();
    let inject_permanent_receive_error = receipt_control.inject_permanent_receive_error();
    let receipt_ownership = Arc::new(Mutex::new(PreExecReceiptOwnership::None));
    let worker_ownership = Arc::clone(&receipt_ownership);
    let receipt_worker = thread::Builder::new()
        .name("legitimacy-pidfd-receipt".to_string())
        .spawn(move || {
            let received = if inject_permanent_receive_error {
                #[cfg(test)]
                {
                    receive_pidfd_permanent_error_test_only(&pidfd_receiver)
                }
                #[cfg(not(test))]
                {
                    receive_pidfd(&pidfd_receiver)
                }
            } else {
                receive_pidfd(&pidfd_receiver)
            };
            match received {
                Ok(pidfd) => {
                    let mut ownership = worker_ownership
                        .lock()
                        .unwrap_or_else(std::sync::PoisonError::into_inner);
                    *ownership = PreExecReceiptOwnership::Accepted(pidfd);
                    drop(ownership);
                    let _ = acknowledge_pidfd_receipt(&pidfd_receiver);
                }
                Err(PidfdReceiveFailure {
                    recovered: Some(pidfd),
                }) => {
                    let mut ownership = worker_ownership
                        .lock()
                        .unwrap_or_else(std::sync::PoisonError::into_inner);
                    *ownership = PreExecReceiptOwnership::Rejected(pidfd);
                }
                Err(PidfdReceiveFailure { recovered: None }) => {}
            }
        })
        .map_err(|_| error(AdapterErrorCodeV0::CaptureSpawn))?;
    let mut command = Command::new("/legitimacy-unused-after-fexecve");
    command
        .env_clear()
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    unsafe {
        command.pre_exec(move || {
            let _keep_argument_storage_alive = (&argv, &environment);
            libc::close(pidfd_receiver_raw);
            #[cfg(test)]
            if send_handleless_before_exec {
                send_pidfd_packet_without_handle(&pidfd_sender)?;
            } else {
                send_self_pidfd(&pidfd_sender)?;
            }
            #[cfg(not(test))]
            send_self_pidfd(&pidfd_sender)?;
            await_pidfd_receipt_ack(&pidfd_sender)?;
            child_signal_state.restore()?;
            rustix::process::setsid()?;
            rustix::process::fchdir(&workspace_fd)?;
            libc::fexecve(
                executable_fd.as_raw_fd(),
                argv_pointers.as_ptr().cast(),
                environment_pointers.as_ptr().cast(),
            );
            Err(std::io::Error::last_os_error())
        });
    }
    let spawned = command.spawn();
    drop(command);
    let _receipt_worker_result = receipt_worker.join();
    let ownership = {
        let mut ownership = receipt_ownership
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        std::mem::replace(&mut *ownership, PreExecReceiptOwnership::None)
    };
    let (mut child, main_pidfd) = match (spawned, ownership) {
        (Ok(child), PreExecReceiptOwnership::Accepted(main_pidfd)) => (child, main_pidfd),
        (Ok(mut child), PreExecReceiptOwnership::Rejected(pidfd)) => {
            return contain_pidfd_receipt_failure(
                &mut child,
                PidfdReceiveFailure {
                    recovered: Some(pidfd),
                },
            );
        }
        (Err(_), _) => {
            return Err(error(AdapterErrorCodeV0::CaptureSpawn));
        }
        (Ok(_), PreExecReceiptOwnership::None) => {
            return Err(error(AdapterErrorCodeV0::CaptureCleanup));
        }
    };
    match receipt_control.finish_after_spawn(main_pidfd) {
        Ok(main_pidfd) => supervise_spawned_child(
            main_pidfd,
            &mut child,
            request.stdin_bytes,
            request.timeout,
            request.stdout_cap,
            request.stderr_cap,
            #[cfg(test)]
            request.writer_start,
        ),
        Err(receipt_failure) => contain_pidfd_receipt_failure(&mut child, receipt_failure),
    }
}
