use super::*;

#[test]
fn fixed_authority_rejects_insertion_deletion_reorder_truncation_and_mutation() {
    let authority = synthetic_authority(COMPLETED);
    let context = trusted(&authority);
    let lines = COMPLETED
        .split_inclusive(|byte| *byte == b'\n')
        .map(<[u8]>::to_vec)
        .collect::<Vec<_>>();
    let mut attacks = Vec::new();

    let mut inserted = lines.clone();
    inserted.insert(
        1,
        b"{\"type\":\"error\",\"message\":\"synthetic inserted\"}\n".to_vec(),
    );
    attacks.push(inserted.into_iter().flatten().collect::<Vec<_>>());

    let mut deleted = lines.clone();
    deleted.remove(1);
    attacks.push(deleted.into_iter().flatten().collect::<Vec<_>>());

    let mut reordered = lines.clone();
    reordered.swap(1, 2);
    attacks.push(reordered.into_iter().flatten().collect::<Vec<_>>());

    attacks.push(COMPLETED[..COMPLETED.len() - 1].to_vec());

    let mut mutated = COMPLETED.to_vec();
    let offset = mutated
        .windows(b"synthetic response".len())
        .position(|window| window == b"synthetic response")
        .unwrap();
    mutated[offset] = b'S';
    attacks.push(mutated);

    for attack in attacks {
        assert!(adapt_codex_exec_v0(&attack, &authority, &context).is_err());
    }
}
