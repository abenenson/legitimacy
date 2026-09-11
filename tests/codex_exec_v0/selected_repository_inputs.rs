use super::source_binding_registry::dep_info_inputs;
use crate::repository_object::{
    INPUT_CONTENT_CHANGED, INPUT_IDENTITY_CHANGED, INPUT_NONREGULAR, INPUT_SYMLINK,
    ROOT_OBJECT_CHANGED, ReadStage, read_repository_file, read_repository_file_with_hook,
};
use std::io::Write;
use std::os::unix::fs::{FileExt, symlink};
use std::time::{SystemTime, UNIX_EPOCH};

#[test]
fn selected_inputs_are_descriptor_bound_regular_repository_objects() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let parent = std::env::temp_dir().join(format!(
        "legitimacy-selected-object-{}-{nonce}",
        std::process::id()
    ));
    let root = parent.join("repository");
    let outside = parent.join("outside");
    std::fs::create_dir_all(root.join("nested")).unwrap();
    std::fs::create_dir_all(&outside).unwrap();
    std::fs::write(outside.join("outside.rs"), b"outside\n").unwrap();
    std::fs::write(root.join("nested/inside.rs"), b"inside\n").unwrap();

    symlink(outside.join("outside.rs"), root.join("compiler.rs")).unwrap();
    let dep_info = parent.join("compiler.d");
    std::fs::write(
        &dep_info,
        format!("output: {}\n", root.join("compiler.rs").display()),
    )
    .unwrap();
    assert_eq!(dep_info_inputs(&root, &dep_info), Err(INPUT_SYMLINK));

    symlink(outside.join("outside.rs"), root.join("Cargo.toml")).unwrap();
    assert_eq!(
        read_repository_file(&root, "Cargo.toml", 1024),
        Err(INPUT_SYMLINK)
    );

    symlink(&outside, root.join("ancestor-alias")).unwrap();
    assert_eq!(
        read_repository_file(&root, "ancestor-alias/outside.rs", 1024),
        Err(INPUT_SYMLINK)
    );
    symlink(root.join("nested/inside.rs"), root.join("inside-alias.rs")).unwrap();
    assert_eq!(
        read_repository_file(&root, "inside-alias.rs", 1024),
        Err(INPUT_SYMLINK)
    );
    std::os::unix::net::UnixListener::bind(root.join("socket-object")).unwrap();
    assert_eq!(
        read_repository_file(&root, "socket-object", 1024),
        Err(INPUT_NONREGULAR)
    );

    let root_parent = parent.join("root-replacement");
    let replaceable_root = root_parent.join("repository");
    std::fs::create_dir_all(replaceable_root.join("nested")).unwrap();
    std::fs::write(replaceable_root.join("nested/input.rs"), b"original\n").unwrap();
    let original_root = replaceable_root.clone();
    let displaced_root = root_parent.join("displaced");
    assert_eq!(
        read_repository_file_with_hook(&replaceable_root, "nested/input.rs", 1024, |stage| {
            if stage == ReadStage::AfterOpen {
                std::fs::rename(&original_root, &displaced_root).unwrap();
                std::fs::create_dir_all(original_root.join("nested")).unwrap();
                std::fs::write(original_root.join("nested/input.rs"), b"replacement\n").unwrap();
            }
        }),
        Err(ROOT_OBJECT_CHANGED)
    );

    let ancestor_root = parent.join("ancestor-replacement");
    std::fs::create_dir_all(ancestor_root.join("nested")).unwrap();
    std::fs::write(ancestor_root.join("nested/input.rs"), b"original\n").unwrap();
    let ancestor_for_hook = ancestor_root.clone();
    assert_eq!(
        read_repository_file_with_hook(&ancestor_root, "nested/input.rs", 1024, |stage| {
            if stage == ReadStage::AfterOpen {
                std::fs::rename(
                    ancestor_for_hook.join("nested"),
                    ancestor_for_hook.join("displaced"),
                )
                .unwrap();
                std::fs::create_dir(ancestor_for_hook.join("nested")).unwrap();
                std::fs::write(ancestor_for_hook.join("nested/input.rs"), b"replacement\n")
                    .unwrap();
            }
        }),
        Err(INPUT_IDENTITY_CHANGED)
    );

    let final_root = parent.join("final-replacement");
    std::fs::create_dir_all(final_root.join("nested")).unwrap();
    std::fs::write(final_root.join("nested/input.rs"), b"original\n").unwrap();
    let final_for_hook = final_root.clone();
    assert_eq!(
        read_repository_file_with_hook(&final_root, "nested/input.rs", 1024, |stage| {
            if stage == ReadStage::AfterOpen {
                std::fs::rename(
                    final_for_hook.join("nested/input.rs"),
                    final_for_hook.join("nested/displaced.rs"),
                )
                .unwrap();
                std::fs::write(final_for_hook.join("nested/input.rs"), b"replacement\n").unwrap();
            }
        }),
        Err(INPUT_IDENTITY_CHANGED)
    );

    let mutation_root = parent.join("content-mutation");
    std::fs::create_dir_all(&mutation_root).unwrap();
    let mutation_path = mutation_root.join("input.rs");
    let mut initial = std::fs::File::create(&mutation_path).unwrap();
    initial.write_all(&vec![b'a'; 64 * 1024]).unwrap();
    drop(initial);
    let mutation_for_hook = mutation_path.clone();
    assert_eq!(
        read_repository_file_with_hook(&mutation_root, "input.rs", 128 * 1024, |stage| {
            if stage == ReadStage::AfterFirstChunk {
                let file = std::fs::OpenOptions::new()
                    .write(true)
                    .open(&mutation_for_hook)
                    .unwrap();
                file.write_all_at(b"changed", 0).unwrap();
            }
        }),
        Err(INPUT_CONTENT_CHANGED)
    );

    std::fs::remove_dir_all(parent).unwrap();
}
