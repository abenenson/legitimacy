use super::*;
use rustix::fs::{RenameFlags, renameat_with};
use sha2::{Digest, Sha256};

pub(super) fn rollback_committed(
    publication: CommittedPublicationV0,
    bytes: &[u8],
) -> Result<(), AdapterErrorV0> {
    rollback_committed_with_hooks(publication, bytes, &mut NoPublicationHooksV0)
}

pub(super) fn rollback_committed_with_hooks(
    publication: CommittedPublicationV0,
    bytes: &[u8],
    hooks: &mut impl PublicationHooksV0,
) -> Result<(), AdapterErrorV0> {
    let uncertain = || error(AdapterErrorCodeV0::OutputRollbackUncertain);
    let expected_len = usize::try_from(fstat(&publication.held).map_err(|_| uncertain())?.st_size)
        .map_err(|_| uncertain())?;
    verify_final_identity(
        &publication.parent_path,
        &publication.name,
        publication.identity,
        publication.metadata,
        publication.expected_uid,
        expected_len,
    )
    .map_err(|_| uncertain())?;
    attempt(
        hooks,
        PublicationStageV0::RollbackQuarantine,
        Some(&publication.held),
    )
    .map_err(|_| uncertain())?;
    let quarantine = rollback_quarantine_name()?;
    renameat_with(
        &publication.parent_path,
        &publication.name,
        &publication.parent_path,
        &quarantine,
        RenameFlags::NOREPLACE,
    )
    .map_err(|_| uncertain())?;
    verify_final_identity(
        &publication.parent_path,
        &quarantine,
        publication.identity,
        None,
        publication.expected_uid,
        expected_len,
    )
    .map_err(|_| uncertain())?;
    verify_quarantined_content(&publication, bytes)?;
    complete(
        hooks,
        PublicationStageV0::RollbackQuarantine,
        Some(&publication.held),
    );
    attempt(
        hooks,
        PublicationStageV0::RollbackBeforeUnlink,
        Some(&publication.held),
    )
    .map_err(|_| uncertain())?;
    verify_final_identity(
        &publication.parent_path,
        &quarantine,
        publication.identity,
        None,
        publication.expected_uid,
        expected_len,
    )
    .map_err(|_| uncertain())?;
    verify_quarantined_content(&publication, bytes)?;
    complete(
        hooks,
        PublicationStageV0::RollbackBeforeUnlink,
        Some(&publication.held),
    );
    unlinkat(&publication.parent_path, &quarantine, AtFlags::empty()).map_err(|_| uncertain())?;
    fsync(&publication.parent_sync).map_err(|_| uncertain())
}

fn verify_quarantined_content(
    publication: &CommittedPublicationV0,
    bytes: &[u8],
) -> Result<(), AdapterErrorV0> {
    let uncertain = || error(AdapterErrorCodeV0::OutputRollbackUncertain);
    let hash = Sha256::digest(bytes);
    verify_held(
        &mut NoPublicationHooksV0,
        &publication.held,
        HeldExpectationV0 {
            bytes,
            hash: &hash,
            uid: publication.expected_uid,
            links: 1,
            property_code: AdapterErrorCodeV0::OutputRollbackUncertain,
            content_code: AdapterErrorCodeV0::OutputRollbackUncertain,
        },
    )
    .map(|_| ())
    .map_err(|_| uncertain())
}

fn rollback_quarantine_name() -> Result<OsString, AdapterErrorV0> {
    let mut random = [0_u8; 16];
    rustix::rand::getrandom(&mut random, rustix::rand::GetRandomFlags::empty())
        .map_err(|_| error(AdapterErrorCodeV0::OutputRollbackUncertain))?;
    if random.iter().all(|byte| *byte == 0) {
        return Err(error(AdapterErrorCodeV0::OutputRollbackUncertain));
    }
    let suffix = random
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    Ok(OsString::from(format!(".rollback-{suffix}.quarantine")))
}
