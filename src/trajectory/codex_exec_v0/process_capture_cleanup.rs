//! Owned process-tree observation, signaling, reaping, and absence proof.

use super::signal::OwnedChildren;
use super::*;
use rustix::process::Signal;
use std::process::{Child, ExitStatus};
use std::thread;
use std::time::Duration;

pub(super) const POLL_INTERVAL: Duration = Duration::from_millis(5);
const TERM_GRACE: Duration = Duration::from_secs(2);
const CLEANUP_CAP: Duration = Duration::from_secs(10);

pub(super) trait SupervisorOperations {
    fn observe(&mut self, owned: &mut OwnedChildren) -> AdapterResultV0<()>;
    fn signal(&mut self, owned: &OwnedChildren, signal: Signal) -> AdapterResultV0<()>;
    fn try_wait(&mut self, child: &mut Child) -> AdapterResultV0<Option<ExitStatus>>;
    fn reap(&mut self, owned: &mut OwnedChildren) -> AdapterResultV0<()>;
    fn absent(&mut self, owned: &mut OwnedChildren) -> AdapterResultV0<bool>;
    fn sleep(&mut self, duration: Duration);
}

pub(super) struct RealSupervisorOperations;

impl SupervisorOperations for RealSupervisorOperations {
    fn observe(&mut self, owned: &mut OwnedChildren) -> AdapterResultV0<()> {
        owned.observe_direct()
    }

    fn signal(&mut self, owned: &OwnedChildren, signal: Signal) -> AdapterResultV0<()> {
        owned.signal(signal)
    }

    fn try_wait(&mut self, child: &mut Child) -> AdapterResultV0<Option<ExitStatus>> {
        child
            .try_wait()
            .map_err(|_| error(AdapterErrorCodeV0::CaptureCleanup))
    }

    fn reap(&mut self, owned: &mut OwnedChildren) -> AdapterResultV0<()> {
        owned.reap_adopted()
    }

    fn absent(&mut self, owned: &mut OwnedChildren) -> AdapterResultV0<bool> {
        owned.fresh_absence()
    }

    fn sleep(&mut self, duration: Duration) {
        thread::sleep(duration);
    }
}

pub(super) fn cleanup_process_tree(
    operations: &mut impl SupervisorOperations,
    child: &mut Child,
    status: &mut Option<ExitStatus>,
    owned: &mut OwnedChildren,
) -> AdapterResultV0<()> {
    if status.is_some() {
        owned.main_reaped();
    }
    let mut uncertain = false;
    for (signal, duration) in [(Signal::TERM, TERM_GRACE), (Signal::KILL, CLEANUP_CAP)] {
        let iterations = duration.as_millis() / POLL_INTERVAL.as_millis();
        for _ in 0..iterations {
            let observed_current_tree = match operations.observe(owned) {
                Ok(()) => true,
                Err(_) => {
                    uncertain = true;
                    false
                }
            };
            if operations.signal(owned, signal).is_err() {
                uncertain = true;
            }
            if status.is_none() {
                match operations.try_wait(child) {
                    Ok(observed) => {
                        *status = observed;
                        if status.is_some() {
                            owned.main_reaped();
                        }
                    }
                    Err(_) => uncertain = true,
                }
            }
            let reaped_current_tree = match operations.reap(owned) {
                Ok(()) => true,
                Err(_) => {
                    uncertain = true;
                    false
                }
            };
            match operations.absent(owned) {
                Ok(true) if status.is_some() && observed_current_tree && reaped_current_tree => {
                    return if uncertain {
                        Err(error(AdapterErrorCodeV0::CaptureCleanup))
                    } else {
                        Ok(())
                    };
                }
                Ok(_) => {}
                Err(_) => uncertain = true,
            }
            operations.sleep(POLL_INTERVAL);
        }
    }
    if operations.observe(owned).is_err() {
        uncertain = true;
    }
    if operations.signal(owned, Signal::KILL).is_err() {
        uncertain = true;
    }
    if status.is_none() {
        match operations.try_wait(child) {
            Ok(observed) => {
                *status = observed;
                if status.is_some() {
                    owned.main_reaped();
                }
            }
            Err(_) => uncertain = true,
        }
    }
    if operations.reap(owned).is_err() {
        uncertain = true;
    }
    let absent = match operations.absent(owned) {
        Ok(value) => value,
        Err(_) => {
            uncertain = true;
            false
        }
    };
    if uncertain || status.is_none() || !absent {
        Err(error(AdapterErrorCodeV0::CaptureCleanup))
    } else {
        Ok(())
    }
}
