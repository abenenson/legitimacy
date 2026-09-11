use super::*;

impl From<AdapterErrorV0> for CommitFailureV0 {
    fn from(error: AdapterErrorV0) -> Self {
        Self::PreLink(error)
    }
}

impl PreparedPublicationV0 {
    fn reject_cross_output_alias(&self, other: &Self) -> Result<(), AdapterErrorV0> {
        if self.parent_identity == other.parent_identity
            && self.name.as_os_str().as_bytes() == other.name.as_os_str().as_bytes()
        {
            Err(error(AdapterErrorCodeV0::CrossOutputAlias))
        } else {
            Ok(())
        }
    }
}

pub(crate) fn publish_pair<F>(
    sidecar_output: &Path,
    sidecar_bytes: &[u8],
    public_output: &Path,
    public_bytes: &[u8],
    inputs: &[&SnapshotV0],
    semantic_pair: F,
) -> Result<(CommittedPublicationV0, CommittedPublicationV0), AdapterErrorV0>
where
    F: FnOnce() -> Result<(), AdapterErrorV0>,
{
    publish_pair_with_hooks(
        PublicationSpecV0 {
            output: sidecar_output,
            bytes: sidecar_bytes,
        },
        PublicationSpecV0 {
            output: public_output,
            bytes: public_bytes,
        },
        inputs,
        &mut NoPublicationHooksV0,
        &mut NoPublicationHooksV0,
        semantic_pair,
    )
}

#[derive(Clone, Copy)]
pub(crate) struct PublicationSpecV0<'a> {
    pub(crate) output: &'a Path,
    pub(crate) bytes: &'a [u8],
}

pub(crate) fn publish_set<F>(
    publications: &[PublicationSpecV0<'_>],
    inputs: &[&SnapshotV0],
    late_verifier: F,
) -> Result<(), AdapterErrorV0>
where
    F: FnOnce() -> Result<(), AdapterErrorV0>,
{
    if publications.is_empty() {
        return Err(error(AdapterErrorCodeV0::OutputPublish));
    }
    let expected_uid = rustix::process::geteuid().as_raw();
    let mut prepared = Vec::with_capacity(publications.len());
    for publication in publications {
        prepared.push(prepare_with_hooks(
            publication.output,
            inputs,
            expected_uid,
            &mut NoPublicationHooksV0,
        )?);
    }
    for (index, left) in prepared.iter().enumerate() {
        for right in &prepared[index + 1..] {
            left.reject_cross_output_alias(right)?;
        }
    }
    revalidate_inputs(inputs)?;

    let mut committed: Vec<(CommittedPublicationV0, &[u8])> =
        Vec::with_capacity(publications.len());
    for (prepared, publication) in prepared.into_iter().zip(publications) {
        let publication_bytes = publication.bytes;
        let protected = committed
            .iter()
            .map(|(publication, _)| publication)
            .collect::<Vec<_>>();
        let result = commit_with_hooks(
            prepared,
            publication_bytes,
            inputs,
            &protected,
            &mut NoPublicationHooksV0,
            || {
                revalidate_inputs(inputs)?;
                for (prior, bytes) in &committed {
                    revalidate_committed(prior, bytes, &mut NoPublicationHooksV0)?;
                }
                Ok(())
            },
        );
        match result {
            Ok(publication) => committed.push((publication, publication_bytes)),
            Err(CommitFailureV0::PreLink(original)) => {
                return rollback_after_error(committed, original);
            }
            Err(CommitFailureV0::PostLink {
                committed: publication,
                error: original,
            }) => {
                committed.push((*publication, publication_bytes));
                return rollback_after_error(committed, original);
            }
        }
    }

    let final_result = late_verifier()
        .and_then(|()| revalidate_inputs(inputs))
        .and_then(|()| {
            for (publication, bytes) in &committed {
                revalidate_committed(publication, bytes, &mut NoPublicationHooksV0)?;
            }
            Ok(())
        });
    match final_result {
        Ok(()) => Ok(()),
        Err(original) => rollback_after_error(committed, original),
    }
}

struct RelativeSetFailureV0 {
    committed: Vec<CommittedPublicationV0>,
    error: AdapterErrorV0,
}

fn publish_relative_set<F>(
    directory: &OwnedFd,
    publications: &[(&str, &[u8])],
    inputs: &[&SnapshotV0],
    late_verifier: F,
) -> Result<Vec<CommittedPublicationV0>, RelativeSetFailureV0>
where
    F: FnOnce() -> Result<(), AdapterErrorV0>,
{
    let expected_uid = rustix::process::geteuid().as_raw();
    let mut prepared = Vec::with_capacity(publications.len());
    for (name, _) in publications {
        prepared.push(
            prepare_relative(directory, name, inputs, expected_uid).map_err(|error| {
                RelativeSetFailureV0 {
                    committed: Vec::new(),
                    error,
                }
            })?,
        );
    }
    revalidate_inputs(inputs).map_err(|error| RelativeSetFailureV0 {
        committed: Vec::new(),
        error,
    })?;
    let mut committed = Vec::with_capacity(publications.len());
    for (prepared, (_, bytes)) in prepared.into_iter().zip(publications) {
        let protected = committed.iter().collect::<Vec<_>>();
        match commit_with_hooks(
            prepared,
            bytes,
            inputs,
            &protected,
            &mut NoPublicationHooksV0,
            || Ok(()),
        ) {
            Ok(publication) => committed.push(publication),
            Err(CommitFailureV0::PreLink(error)) => {
                return Err(RelativeSetFailureV0 { committed, error });
            }
            Err(CommitFailureV0::PostLink {
                committed: publication,
                error,
            }) => {
                committed.push(*publication);
                return Err(RelativeSetFailureV0 { committed, error });
            }
        }
    }
    if let Err(error) = late_verifier() {
        return Err(RelativeSetFailureV0 { committed, error });
    }
    if let Err(error) = revalidate_inputs(inputs) {
        return Err(RelativeSetFailureV0 { committed, error });
    }
    for (publication, (_, bytes)) in committed.iter().zip(publications) {
        if let Err(error) = revalidate_committed(publication, bytes, &mut NoPublicationHooksV0) {
            return Err(RelativeSetFailureV0 { committed, error });
        }
    }
    Ok(committed)
}

fn revalidate_inputs(inputs: &[&SnapshotV0]) -> Result<(), AdapterErrorV0> {
    for input in inputs {
        input.revalidate()?;
    }
    Ok(())
}

fn rollback_after_error(
    mut committed: Vec<(CommittedPublicationV0, &[u8])>,
    original: AdapterErrorV0,
) -> Result<(), AdapterErrorV0> {
    let mut rollback_failed = false;
    while let Some((publication, bytes)) = committed.pop() {
        if rollback_committed(publication, bytes).is_err() {
            rollback_failed = true;
        }
    }
    if rollback_failed {
        Err(error(AdapterErrorCodeV0::OutputRollbackUncertain))
    } else {
        Err(original)
    }
}

#[path = "linux_output_set.rs"]
mod output_set;
pub(crate) use output_set::publish_directory_set;

#[cfg(test)]
#[path = "linux_output_set_tests.rs"]
mod output_set_tests;

pub(super) fn publish_pair_with_hooks<F>(
    sidecar: PublicationSpecV0<'_>,
    public: PublicationSpecV0<'_>,
    inputs: &[&SnapshotV0],
    sidecar_hooks: &mut impl PublicationHooksV0,
    public_hooks: &mut impl PublicationHooksV0,
    semantic_pair: F,
) -> Result<(CommittedPublicationV0, CommittedPublicationV0), AdapterErrorV0>
where
    F: FnOnce() -> Result<(), AdapterErrorV0>,
{
    semantic_pair()?;
    if sidecar.output.as_os_str().as_bytes() == public.output.as_os_str().as_bytes() {
        return Err(error(AdapterErrorCodeV0::CrossOutputAlias));
    }
    let expected_uid = rustix::process::geteuid().as_raw();
    let sidecar_bytes = sidecar.bytes;
    let public_bytes = public.bytes;
    let sidecar_prepared = prepare_with_hooks(sidecar.output, inputs, expected_uid, sidecar_hooks)?;
    let public_prepared = prepare_with_hooks(public.output, inputs, expected_uid, public_hooks)?;
    sidecar_prepared.reject_cross_output_alias(&public_prepared)?;

    let sidecar = match commit_with_hooks(
        sidecar_prepared,
        sidecar_bytes,
        inputs,
        &[],
        sidecar_hooks,
        || Ok(()),
    ) {
        Ok(committed) => committed,
        Err(CommitFailureV0::PreLink(error)) => return Err(error),
        Err(CommitFailureV0::PostLink {
            committed,
            error: original,
        }) => {
            let revalidation = revalidate_committed(&committed, sidecar_bytes, sidecar_hooks).err();
            let error = rank_errors([Some(original), revalidation]);
            drop(committed);
            return Err(error);
        }
    };

    let public_result = commit_with_hooks(
        public_prepared,
        public_bytes,
        inputs,
        &[&sidecar],
        public_hooks,
        || revalidate_committed(&sidecar, sidecar_bytes, sidecar_hooks),
    );
    match public_result {
        Err(CommitFailureV0::PreLink(public_error)) => {
            let sidecar_error = revalidate_committed(&sidecar, sidecar_bytes, sidecar_hooks).err();
            let error = if public_error.code() == AdapterErrorCodeV0::CrossOutputAlias {
                public_error
            } else if sidecar_error.is_some() {
                rank_errors([sidecar_error, Some(public_error)])
            } else {
                public_error
            };
            drop(sidecar);
            Err(error)
        }
        Err(CommitFailureV0::PostLink {
            committed: public,
            error: original,
        }) => {
            let sidecar_error = revalidate_committed(&sidecar, sidecar_bytes, sidecar_hooks).err();
            let public_error = revalidate_committed(&public, public_bytes, public_hooks).err();
            let error = rank_errors([Some(original), sidecar_error, public_error]);
            drop(public);
            drop(sidecar);
            Err(error)
        }
        Ok(public) => {
            let sidecar_error = revalidate_committed(&sidecar, sidecar_bytes, sidecar_hooks).err();
            let public_error = revalidate_committed(&public, public_bytes, public_hooks).err();
            if sidecar_error.is_some() || public_error.is_some() {
                let error = rank_errors([sidecar_error, public_error]);
                drop(public);
                drop(sidecar);
                Err(error)
            } else {
                Ok((sidecar, public))
            }
        }
    }
}

fn revalidate_committed(
    committed: &CommittedPublicationV0,
    bytes: &[u8],
    hooks: &mut impl PublicationHooksV0,
) -> Result<(), AdapterErrorV0> {
    let hash = Sha256::digest(bytes);
    let euid = attempt(
        hooks,
        PublicationStageV0::CommittedEuidRevalidate,
        Some(&committed.held),
    )
    .map_err(|_| error(AdapterErrorCodeV0::OutputIdentityUncertain))
    .and_then(|()| {
        if rustix::process::geteuid().as_raw() == committed.expected_uid {
            Ok(())
        } else {
            Err(error(AdapterErrorCodeV0::OutputIdentityUncertain))
        }
    });
    if euid.is_ok() {
        complete(
            hooks,
            PublicationStageV0::CommittedEuidRevalidate,
            Some(&committed.held),
        );
    }
    let integrity = attempt(
        hooks,
        PublicationStageV0::CommittedIntegrityRevalidate,
        Some(&committed.held),
    )
    .map_err(|_| error(AdapterErrorCodeV0::OutputIntegrityUncertain))
    .and_then(|()| {
        verify_held(
            hooks,
            &committed.held,
            HeldExpectationV0 {
                bytes,
                hash: &hash,
                uid: committed.expected_uid,
                links: 1,
                property_code: AdapterErrorCodeV0::OutputIntegrityUncertain,
                content_code: AdapterErrorCodeV0::OutputIntegrityUncertain,
            },
        )
        .and_then(|metadata| {
            if committed.metadata == Some(metadata) {
                Ok(())
            } else {
                Err(error(AdapterErrorCodeV0::OutputIntegrityUncertain))
            }
        })
    });
    if integrity.is_ok() {
        complete(
            hooks,
            PublicationStageV0::CommittedIntegrityRevalidate,
            Some(&committed.held),
        );
    }

    let identity = attempt(
        hooks,
        PublicationStageV0::CommittedIdentityRevalidate,
        Some(&committed.held),
    )
    .map_err(|_| error(AdapterErrorCodeV0::OutputIdentityUncertain))
    .and_then(|()| {
        verify_final_identity(
            &committed.parent_path,
            &committed.name,
            committed.identity,
            committed.metadata,
            committed.expected_uid,
            bytes.len(),
        )
    });
    if identity.is_ok() {
        complete(
            hooks,
            PublicationStageV0::CommittedIdentityRevalidate,
            Some(&committed.held),
        );
    }
    if euid.is_err() || identity.is_err() {
        Err(error(AdapterErrorCodeV0::OutputIdentityUncertain))
    } else if integrity.is_err() {
        Err(error(AdapterErrorCodeV0::OutputIntegrityUncertain))
    } else {
        Ok(())
    }
}

fn rank_errors<const N: usize>(errors: [Option<AdapterErrorV0>; N]) -> AdapterErrorV0 {
    let mut selected = None;
    let mut selected_rank = 0;
    for error in errors.into_iter().flatten() {
        let rank = committed_error_rank(error.code());
        if selected.is_none() || rank > selected_rank {
            selected = Some(error);
            selected_rank = rank;
        }
    }
    selected.unwrap_or_else(|| error(AdapterErrorCodeV0::OutputPublish))
}

fn committed_error_rank(code: AdapterErrorCodeV0) -> u8 {
    match code {
        AdapterErrorCodeV0::OutputIdentityUncertain => 3,
        AdapterErrorCodeV0::OutputIntegrityUncertain => 2,
        AdapterErrorCodeV0::DurabilityUncertain => 1,
        _ => 0,
    }
}

#[cfg(test)]
#[path = "linux_output_transaction_tests.rs"]
mod tests;
