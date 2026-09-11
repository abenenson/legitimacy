//! Nonrecyclable Linux signal authority and subreaper-child closure.

use super::*;
use rustix::fd::{AsFd, OwnedFd};
use rustix::net::{
    AddressFamily, RecvAncillaryBuffer, RecvAncillaryMessage, RecvFlags, SendAncillaryBuffer,
    SendAncillaryMessage, SendFlags, SocketFlags, SocketType, recvmsg, sendmsg, socketpair,
};
use rustix::process::{
    Pid, PidfdFlags, Signal, WaitId, WaitIdOptions, pidfd_open, pidfd_send_signal, waitid,
};
use std::collections::BTreeMap;
use std::io::{IoSlice, IoSliceMut};
use std::mem::MaybeUninit;

pub(super) struct ChildSignalBoundary {
    original_mask: libc::sigset_t,
    original_action: libc::sigaction,
    active: bool,
}

pub(super) struct ChildSignalState {
    original_mask: libc::sigset_t,
    original_action: libc::sigaction,
}

impl ChildSignalBoundary {
    pub(super) fn enter() -> AdapterResultV0<Self> {
        unsafe {
            let mut blocked = std::mem::zeroed();
            if libc::sigemptyset(&mut blocked) != 0
                || libc::sigaddset(&mut blocked, libc::SIGCHLD) != 0
            {
                return Err(error(AdapterErrorCodeV0::CaptureSpawn));
            }
            let mut original_mask = std::mem::zeroed();
            let mask_result = libc::pthread_sigmask(libc::SIG_BLOCK, &blocked, &mut original_mask);
            if mask_result != 0 {
                return Err(error(AdapterErrorCodeV0::CaptureSpawn));
            }
            let mut original_action = std::mem::zeroed();
            if libc::sigaction(libc::SIGCHLD, std::ptr::null(), &mut original_action) != 0 {
                let _ =
                    libc::pthread_sigmask(libc::SIG_SETMASK, &original_mask, std::ptr::null_mut());
                return Err(error(AdapterErrorCodeV0::CaptureSpawn));
            }
            let mut default_action: libc::sigaction = std::mem::zeroed();
            default_action.sa_sigaction = libc::SIG_DFL;
            if libc::sigemptyset(&mut default_action.sa_mask) != 0
                || libc::sigaction(libc::SIGCHLD, &default_action, std::ptr::null_mut()) != 0
            {
                let _ =
                    libc::pthread_sigmask(libc::SIG_SETMASK, &original_mask, std::ptr::null_mut());
                return Err(error(AdapterErrorCodeV0::CaptureSpawn));
            }
            Ok(Self {
                original_mask,
                original_action,
                active: true,
            })
        }
    }

    pub(super) fn child_state(&self) -> ChildSignalState {
        unsafe {
            ChildSignalState {
                original_mask: std::ptr::read(&self.original_mask),
                original_action: std::ptr::read(&self.original_action),
            }
        }
    }

    pub(super) fn restore(mut self) -> AdapterResultV0<()> {
        restore_signal_state(&self.original_mask, &self.original_action)
            .map_err(|_| error(AdapterErrorCodeV0::CaptureCleanup))?;
        self.active = false;
        Ok(())
    }
}

impl Drop for ChildSignalBoundary {
    fn drop(&mut self) {
        if self.active {
            let _ = restore_signal_state(&self.original_mask, &self.original_action);
        }
    }
}

impl ChildSignalState {
    pub(super) fn restore(&self) -> std::io::Result<()> {
        restore_signal_state(&self.original_mask, &self.original_action)
    }
}

fn restore_signal_state(
    original_mask: &libc::sigset_t,
    original_action: &libc::sigaction,
) -> std::io::Result<()> {
    unsafe {
        let action_result = libc::sigaction(libc::SIGCHLD, original_action, std::ptr::null_mut());
        let action_error = (action_result != 0).then(std::io::Error::last_os_error);
        let mask_result =
            libc::pthread_sigmask(libc::SIG_SETMASK, original_mask, std::ptr::null_mut());
        if let Some(action_error) = action_error {
            Err(action_error)
        } else if mask_result != 0 {
            Err(std::io::Error::from_raw_os_error(mask_result))
        } else {
            Ok(())
        }
    }
}

pub(super) fn pidfd_channel() -> AdapterResultV0<(OwnedFd, OwnedFd)> {
    socketpair(
        AddressFamily::UNIX,
        SocketType::SEQPACKET,
        SocketFlags::CLOEXEC,
        None,
    )
    .map_err(|_| error(AdapterErrorCodeV0::CaptureSpawn))
}

pub(super) fn send_self_pidfd(socket: &OwnedFd) -> std::io::Result<()> {
    let pidfd = pidfd_open(rustix::process::getpid(), PidfdFlags::empty())?;
    let descriptors = [pidfd.as_fd()];
    let mut space = [MaybeUninit::uninit(); rustix::cmsg_space!(ScmRights(1))];
    let mut ancillary = SendAncillaryBuffer::new(&mut space);
    if !ancillary.push(SendAncillaryMessage::ScmRights(&descriptors)) {
        return Err(std::io::Error::from_raw_os_error(libc::EINVAL));
    }
    let payload = [IoSlice::new(b"P")];
    if sendmsg(socket, &payload, &mut ancillary, SendFlags::empty())? != 1 {
        return Err(std::io::Error::from_raw_os_error(libc::EIO));
    }
    Ok(())
}

#[cfg(test)]
pub(super) fn send_pidfd_packet_without_handle(socket: &OwnedFd) -> std::io::Result<()> {
    if rustix::io::write(socket, b"P")? != 1 {
        return Err(std::io::Error::from_raw_os_error(libc::EIO));
    }
    Ok(())
}

pub(super) struct PidfdReceiveFailure {
    pub(super) recovered: Option<OwnedFd>,
}

pub(super) fn receive_pidfd(socket: &OwnedFd) -> Result<OwnedFd, PidfdReceiveFailure> {
    receive_pidfd_inner(socket, false)
}

#[cfg(test)]
pub(super) fn receive_pidfd_permanent_error_test_only(
    socket: &OwnedFd,
) -> Result<OwnedFd, PidfdReceiveFailure> {
    receive_pidfd_inner(socket, true)
}

fn receive_pidfd_inner(
    socket: &OwnedFd,
    inject_permanent_error: bool,
) -> Result<OwnedFd, PidfdReceiveFailure> {
    let mut byte = [0_u8; 1];
    let mut payload = [IoSliceMut::new(&mut byte)];
    let mut space = [MaybeUninit::uninit(); rustix::cmsg_space!(ScmRights(1))];
    let mut ancillary = RecvAncillaryBuffer::new(&mut space);
    let received = loop {
        let outcome = if inject_permanent_error {
            Err(rustix::io::Errno::IO)
        } else {
            recvmsg(
                socket,
                &mut payload,
                &mut ancillary,
                RecvFlags::CMSG_CLOEXEC,
            )
        };
        match outcome {
            Ok(received) => break received,
            Err(rustix::io::Errno::INTR) => continue,
            Err(_) => {
                return Err(PidfdReceiveFailure { recovered: None });
            }
        }
    };
    let mut pidfd = None;
    let mut malformed = received.bytes != 1
        || byte != *b"P"
        || received.flags != rustix::net::ReturnFlags::CMSG_CLOEXEC;
    for message in ancillary.drain() {
        let RecvAncillaryMessage::ScmRights(descriptors) = message else {
            malformed = true;
            continue;
        };
        for descriptor in descriptors {
            if pidfd.replace(descriptor).is_some() {
                malformed = true;
            }
        }
    }
    if let Some(pidfd) = pidfd {
        if malformed {
            return Err(PidfdReceiveFailure {
                recovered: Some(pidfd),
            });
        }
        return Ok(pidfd);
    }
    Err(PidfdReceiveFailure { recovered: None })
}

pub(super) fn acknowledge_pidfd_receipt(socket: &OwnedFd) -> std::io::Result<()> {
    if rustix::io::write(socket, b"A")? != 1 {
        return Err(std::io::Error::from_raw_os_error(libc::EIO));
    }
    Ok(())
}

pub(super) fn await_pidfd_receipt_ack(socket: &OwnedFd) -> std::io::Result<()> {
    let mut byte = [0_u8; 1];
    loop {
        match rustix::io::read(socket, &mut byte) {
            Ok(1) if byte == *b"A" => return Ok(()),
            Ok(_) => return Err(std::io::Error::from_raw_os_error(libc::EIO)),
            Err(rustix::io::Errno::INTR) => {}
            Err(error) => return Err(error.into()),
        }
    }
}

struct OwnedChild {
    pidfd: OwnedFd,
    main: bool,
}

pub(super) struct OwnedChildren {
    children: BTreeMap<u32, OwnedChild>,
}

impl OwnedChildren {
    pub(super) fn new(main: u32, pidfd: OwnedFd) -> Self {
        Self {
            children: BTreeMap::from([(main, OwnedChild { pidfd, main: true })]),
        }
    }

    pub(super) fn observe_direct(&mut self) -> AdapterResultV0<()> {
        for raw_pid in direct_child_pids()? {
            let child_id =
                u32::try_from(raw_pid).map_err(|_| error(AdapterErrorCodeV0::CaptureCleanup))?;
            if self.children.contains_key(&child_id) {
                continue;
            }
            let pid =
                Pid::from_raw(raw_pid).ok_or_else(|| error(AdapterErrorCodeV0::CaptureCleanup))?;
            let pidfd = pidfd_open(pid, PidfdFlags::empty())
                .map_err(|_| error(AdapterErrorCodeV0::CaptureCleanup))?;
            self.children
                .insert(child_id, OwnedChild { pidfd, main: false });
        }
        Ok(())
    }

    pub(super) fn signal(&self, signal: Signal) -> AdapterResultV0<()> {
        let mut uncertain = false;
        for child in self.children.values() {
            match pidfd_send_signal(&child.pidfd, signal) {
                Ok(()) | Err(rustix::io::Errno::SRCH) => {}
                Err(_) => uncertain = true,
            }
        }
        if uncertain {
            Err(error(AdapterErrorCodeV0::CaptureCleanup))
        } else {
            Ok(())
        }
    }

    pub(super) fn main_reaped(&mut self) {
        self.children.retain(|_, child| !child.main);
    }

    pub(super) fn reap_adopted(&mut self) -> AdapterResultV0<()> {
        let mut reaped = Vec::new();
        let mut uncertain = false;
        for (pid, child) in &self.children {
            if child.main {
                continue;
            }
            match waitid(
                WaitId::PidFd(child.pidfd.as_fd()),
                WaitIdOptions::EXITED | WaitIdOptions::NOHANG,
            ) {
                Ok(Some(_)) => reaped.push(*pid),
                Ok(None) => {}
                Err(_) => uncertain = true,
            }
        }
        for pid in reaped {
            self.children.remove(&pid);
        }
        if uncertain {
            Err(error(AdapterErrorCodeV0::CaptureCleanup))
        } else {
            Ok(())
        }
    }

    pub(super) fn fresh_absence(&mut self) -> AdapterResultV0<bool> {
        self.observe_direct()?;
        Ok(self.children.is_empty())
    }

    #[cfg(test)]
    pub(super) fn len(&self) -> usize {
        self.children.len()
    }

    #[cfg(test)]
    pub(super) fn contains_pid(&self, pid: i32) -> bool {
        u32::try_from(pid)
            .ok()
            .is_some_and(|pid| self.children.contains_key(&pid))
    }
}

pub(super) fn direct_child_pids() -> AdapterResultV0<Vec<i32>> {
    let pid = std::process::id();
    let content = std::fs::read_to_string(format!("/proc/self/task/{pid}/children"))
        .map_err(|_| error(AdapterErrorCodeV0::CaptureCleanup))?;
    content
        .split_whitespace()
        .map(|value| {
            value
                .parse()
                .map_err(|_| error(AdapterErrorCodeV0::CaptureCleanup))
        })
        .collect()
}

#[cfg(test)]
#[path = "process_capture_signal_tests.rs"]
mod tests;
