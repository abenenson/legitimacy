use super::*;
use rustix::io::fcntl_setfd;
use std::cell::Cell;
use std::fs;
use std::io::Write;
use std::os::unix::ffi::OsStringExt;
use std::os::unix::fs::{PermissionsExt, symlink};
use std::os::unix::net::UnixListener;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, MutexGuard};

static NEXT: AtomicU64 = AtomicU64::new(0);
static FILESYSTEM_TEST_LOCK: Mutex<()> = Mutex::new(());
type StagingReadHook<'a> = Box<dyn FnMut(&[u8], usize) + 'a>;

struct TestHooks<'a> {
    ancestor: Box<dyn FnMut(usize) + 'a>,
    final_open: Box<dyn FnMut() + 'a>,
    first_chunk: Box<dyn FnMut() + 'a>,
    staging_read: StagingReadHook<'a>,
    proc_root: Option<PathBuf>,
    proc_probe: Option<Box<dyn Fn() + 'a>>,
}

impl Default for TestHooks<'_> {
    fn default() -> Self {
        Self {
            ancestor: Box::new(|_| {}),
            final_open: Box::new(|| {}),
            first_chunk: Box::new(|| {}),
            staging_read: Box::new(|_, _| {}),
            proc_root: None,
            proc_probe: None,
        }
    }
}

impl SnapshotHooksV0 for TestHooks<'_> {
    fn before_ancestor_open(&mut self, index: usize) {
        (self.ancestor)(index);
    }

    fn before_final_open(&mut self) {
        (self.final_open)();
    }

    fn after_first_chunk(&mut self) {
        (self.first_chunk)();
    }

    fn after_staging_read(&mut self, staging: &[u8], read: usize) {
        (self.staging_read)(staging, read);
    }

    fn proc_root(&self) -> &Path {
        if let Some(probe) = &self.proc_probe {
            probe();
        }
        self.proc_root
            .as_deref()
            .unwrap_or_else(|| Path::new("/proc"))
    }
}

#[test]
fn path_syntax_codes_are_exact_and_success_preserves_linux_path_forms() {
    let _guard = filesystem_test_guard();
    let root = temp_directory("syntax");
    let ordinary = root.join("ordinary");
    fs::write(&ordinary, b"payload").unwrap();
    assert_snapshot(&ordinary, 7, b"payload");

    let repeated = OsString::from_vec(
        ordinary
            .as_os_str()
            .as_bytes()
            .iter()
            .flat_map(|byte| {
                if *byte == b'/' {
                    b"//".as_slice()
                } else {
                    std::slice::from_ref(byte)
                }
            })
            .copied()
            .collect(),
    );
    assert_snapshot(Path::new(&repeated), 7, b"payload");

    let relative_root = Path::new("target").join(format!(
        "legitimacy-linux-relative-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir_all(&relative_root).unwrap();
    let relative = relative_root.join("input");
    fs::write(&relative, b"relative").unwrap();
    assert_snapshot(&relative, 8, b"relative");
    let leading_dot = PathBuf::from(".").join(&relative);
    assert_snapshot(&leading_dot, 8, b"relative");
    let internal_dot = PathBuf::from(format!(
        "{}/./input",
        relative_root.as_os_str().to_string_lossy()
    ));
    assert_snapshot(&internal_dot, 8, b"relative");

    let one_component = PathBuf::from(format!(
        "legitimacy-linux-one-component-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::write(&one_component, b"one").unwrap();
    assert_snapshot(&one_component, 3, b"one");

    let non_utf8 = root.join(OsString::from_vec(b"non-utf8-\xff".to_vec()));
    fs::write(&non_utf8, b"bytes").unwrap();
    assert_snapshot(&non_utf8, 5, b"bytes");

    for unsafe_path in [
        PathBuf::new(),
        PathBuf::from("../input"),
        PathBuf::from("../"),
        PathBuf::from("../."),
        PathBuf::from("/../"),
        PathBuf::from("a/../"),
        PathBuf::from("a/../b"),
        PathBuf::from("input/.."),
        PathBuf::from(OsString::from_vec(b"nul\0name".to_vec())),
    ] {
        assert_code(
            read_snapshot(&unsafe_path, 8),
            AdapterErrorCodeV0::UnsafeInputPath,
        );
    }
    for directory_request in [
        PathBuf::from("/"),
        PathBuf::from("."),
        PathBuf::from("./"),
        PathBuf::from(format!("{}/", ordinary.display())),
        PathBuf::from(format!("{}/.", ordinary.display())),
    ] {
        assert_code(
            read_snapshot(&directory_request, 8),
            AdapterErrorCodeV0::InputType,
        );
    }
    let overlong = root.join(OsString::from_vec(vec![b'x'; 256]));
    assert_code(read_snapshot(&overlong, 8), AdapterErrorCodeV0::InputOpen);

    fs::remove_file(one_component).unwrap();
    fs::remove_dir_all(relative_root).unwrap();
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn preexisting_ancestor_and_final_types_are_distinguished_without_opening_them() {
    let _guard = filesystem_test_guard();
    let root = temp_directory("initial-types");
    let directory = root.join("directory");
    fs::create_dir(&directory).unwrap();
    let regular = directory.join("regular");
    fs::write(&regular, b"x").unwrap();

    let ancestor_link = root.join("ancestor-link");
    symlink(&directory, &ancestor_link).unwrap();
    assert_code(
        read_snapshot(&ancestor_link.join("regular"), 8),
        AdapterErrorCodeV0::InputSymlink,
    );
    assert_code(
        read_snapshot(&regular.join("child"), 8),
        AdapterErrorCodeV0::InputType,
    );

    let final_link = root.join("final-link");
    symlink(&regular, &final_link).unwrap();
    assert_code(
        read_snapshot(&final_link, 8),
        AdapterErrorCodeV0::InputSymlink,
    );
    assert_code(read_snapshot(&directory, 8), AdapterErrorCodeV0::InputType);
    assert_code(
        read_snapshot(Path::new("/dev/null"), 8),
        AdapterErrorCodeV0::InputType,
    );

    let socket = root.join("socket");
    let listener = UnixListener::bind(&socket).unwrap();
    assert_code(read_snapshot(&socket, 8), AdapterErrorCodeV0::InputType);

    let all_types = [
        FileType::RegularFile,
        FileType::Directory,
        FileType::Symlink,
        FileType::Fifo,
        FileType::Socket,
        FileType::CharacterDevice,
        FileType::BlockDevice,
        FileType::Unknown,
    ];
    for expected_type in [FileType::Directory, FileType::RegularFile] {
        for actual_type in all_types {
            let expected_code = if actual_type == expected_type {
                None
            } else if actual_type == FileType::Symlink {
                Some(AdapterErrorCodeV0::InputSymlink)
            } else {
                Some(AdapterErrorCodeV0::InputType)
            };
            assert_eq!(
                initial_type_error(actual_type, expected_type),
                expected_code,
                "{actual_type:?} as {expected_type:?}"
            );
        }
    }
    drop(listener);
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn every_ancestor_stat_open_swap_is_input_changed_and_fires_only_its_index() {
    let _guard = filesystem_test_guard();
    for replacement_kind in ["directory", "symlink"] {
        for attack_index in 0..3 {
            let root = temp_directory(&format!("ancestor-swap-{replacement_kind}-{attack_index}"));
            let ancestors = [root.join("a"), root.join("a/b"), root.join("a/b/c")];
            fs::create_dir_all(&ancestors[2]).unwrap();
            let input = ancestors[2].join("input");
            fs::write(&input, b"old").unwrap();
            let hook_attack_index = input
                .components()
                .filter(|component| matches!(component, Component::Normal(_)))
                .count()
                - 4
                + attack_index;
            let target = ancestors[attack_index].clone();
            let moved = root.join(format!("moved-{attack_index}"));
            let calls = Rc::new(Cell::new(0));
            let calls_in_hook = Rc::clone(&calls);
            let mut hooks = TestHooks {
                ancestor: Box::new(move |index| {
                    if index == hook_attack_index {
                        calls_in_hook.set(calls_in_hook.get() + 1);
                        fs::rename(&target, &moved).unwrap();
                        if replacement_kind == "directory" {
                            fs::create_dir(&target).unwrap();
                        } else {
                            symlink(&moved, &target).unwrap();
                        }
                    }
                }),
                ..TestHooks::default()
            };
            assert_code(
                read_snapshot_with_hooks(&input, 8, &mut hooks),
                AdapterErrorCodeV0::InputChanged,
            );
            assert_eq!(calls.get(), 1, "attack index {attack_index}");
            fs::remove_dir_all(root).unwrap();
        }
    }
}

#[test]
fn unrelated_sibling_creation_preserves_pinned_ancestor_identity() {
    let _guard = filesystem_test_guard();
    let root = temp_directory("ancestor-content");
    let directory = root.join("input-directory");
    fs::create_dir(&directory).unwrap();
    let input = directory.join("input");
    fs::write(&input, b"stable").unwrap();

    let root_name = root.file_name().unwrap();
    let mutation_index = parse_path(&input)
        .unwrap()
        .ancestors
        .iter()
        .position(|component| component == root_name)
        .unwrap();
    let sibling = root.join("unrelated");
    let sibling_in_hook = sibling.clone();
    let calls = Rc::new(Cell::new(0));
    let calls_in_hook = Rc::clone(&calls);
    let mut hooks = TestHooks {
        ancestor: Box::new(move |index| {
            if index == mutation_index {
                calls_in_hook.set(calls_in_hook.get() + 1);
                fs::write(&sibling_in_hook, b"concurrent").unwrap();
            }
        }),
        ..TestHooks::default()
    };

    let snapshot = read_snapshot_with_hooks(&input, 6, &mut hooks).unwrap();
    assert_eq!(snapshot.bytes.as_slice(), b"stable");
    assert_eq!(calls.get(), 1);
    assert_eq!(fs::read(sibling).unwrap(), b"concurrent");
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn replacement_after_ancestor_pin_cannot_redirect_the_pinned_walk() {
    let _guard = filesystem_test_guard();
    let root = temp_directory("after-pin");
    let old = root.join("a/b/c");
    fs::create_dir_all(&old).unwrap();
    let input = old.join("input");
    fs::write(&input, b"old-tree").unwrap();
    let original_a = root.join("a");
    let moved_a = root.join("moved-a");
    let replacement = root.join("a/b/c");
    let replacement_hook_index = input
        .components()
        .filter(|component| matches!(component, Component::Normal(_)))
        .count()
        - 3;
    let calls = Rc::new(Cell::new(0));
    let calls_in_hook = Rc::clone(&calls);
    let mut hooks = TestHooks {
        ancestor: Box::new(move |index| {
            if index == replacement_hook_index {
                calls_in_hook.set(calls_in_hook.get() + 1);
                fs::rename(&original_a, &moved_a).unwrap();
                fs::create_dir_all(&replacement).unwrap();
                fs::write(replacement.join("input"), b"replacement-tree").unwrap();
            }
        }),
        ..TestHooks::default()
    };
    let snapshot = read_snapshot_with_hooks(&input, 64, &mut hooks).unwrap();
    assert_eq!(snapshot.bytes.as_slice(), b"old-tree");
    assert_eq!(calls.get(), 1);
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn final_stat_open_substitutions_are_input_changed_without_driver_open() {
    let _guard = filesystem_test_guard();
    for kind in ["symlink", "regular"] {
        let root = temp_directory(&format!("final-swap-{kind}"));
        let input = root.join("input");
        let moved = root.join("moved");
        fs::write(&input, b"old").unwrap();
        let input_in_hook = input.clone();
        let calls = Rc::new(Cell::new(0));
        let calls_in_hook = Rc::clone(&calls);
        let mut hooks = TestHooks {
            final_open: Box::new(move || {
                calls_in_hook.set(calls_in_hook.get() + 1);
                fs::rename(&input_in_hook, &moved).unwrap();
                match kind {
                    "symlink" => symlink(&moved, &input_in_hook).unwrap(),
                    "regular" => fs::write(&input_in_hook, b"new").unwrap(),
                    _ => unreachable!(),
                }
            }),
            ..TestHooks::default()
        };
        assert_code(
            read_snapshot_with_hooks(&input, 8, &mut hooks),
            AdapterErrorCodeV0::InputChanged,
        );
        assert_eq!(calls.get(), 1);
        fs::remove_dir_all(root).unwrap();
    }

    let root = temp_directory("final-swap-socket");
    let input = root.join("input");
    let moved = root.join("moved");
    fs::write(&input, b"old").unwrap();
    let input_in_hook = input.clone();
    let calls = Rc::new(Cell::new(0));
    let calls_in_hook = Rc::clone(&calls);
    let mut listener = None;
    let mut hooks = TestHooks {
        final_open: Box::new(|| {}),
        ..TestHooks::default()
    };
    hooks.final_open = Box::new(|| {
        calls_in_hook.set(calls_in_hook.get() + 1);
        fs::rename(&input_in_hook, &moved).unwrap();
        listener = Some(UnixListener::bind(&input_in_hook).unwrap());
    });
    assert_code(
        read_snapshot_with_hooks(&input, 8, &mut hooks),
        AdapterErrorCodeV0::InputChanged,
    );
    assert_eq!(calls.get(), 1);
    drop(hooks);
    drop(listener);
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn real_mid_read_name_and_same_inode_mutations_are_detected_exactly_once() {
    let _guard = filesystem_test_guard();
    for mutation in ["name", "append", "truncate", "overwrite", "chmod", "nlink"] {
        let root = temp_directory(&format!("mid-read-{mutation}"));
        let input = root.join("input");
        let moved = root.join("moved");
        let link = root.join("link");
        fs::write(&input, vec![b'x'; READ_CHUNK_BYTES * 2 + 17]).unwrap();
        if mutation == "overwrite" {
            let file = fs::OpenOptions::new().write(true).open(&input).unwrap();
            file.set_times(
                fs::FileTimes::new()
                    .set_modified(std::time::UNIX_EPOCH + std::time::Duration::from_secs(1)),
            )
            .unwrap();
        }
        let input_in_hook = input.clone();
        let calls = Rc::new(Cell::new(0));
        let calls_in_hook = Rc::clone(&calls);
        let mut hooks = TestHooks {
            first_chunk: Box::new(move || {
                calls_in_hook.set(calls_in_hook.get() + 1);
                match mutation {
                    "name" => {
                        fs::rename(&input_in_hook, &moved).unwrap();
                        fs::write(&input_in_hook, b"replacement").unwrap();
                    }
                    "append" => fs::OpenOptions::new()
                        .append(true)
                        .open(&input_in_hook)
                        .unwrap()
                        .write_all(b"!")
                        .unwrap(),
                    "truncate" => fs::OpenOptions::new()
                        .write(true)
                        .open(&input_in_hook)
                        .unwrap()
                        .set_len(1)
                        .unwrap(),
                    "overwrite" => fs::OpenOptions::new()
                        .write(true)
                        .open(&input_in_hook)
                        .unwrap()
                        .write_all(b"same-length-change")
                        .unwrap(),
                    "chmod" => {
                        let mut permissions = fs::metadata(&input_in_hook).unwrap().permissions();
                        permissions.set_mode(0o400);
                        fs::set_permissions(&input_in_hook, permissions).unwrap();
                    }
                    "nlink" => fs::hard_link(&input_in_hook, &link).unwrap(),
                    _ => unreachable!(),
                }
            }),
            ..TestHooks::default()
        };
        let result = read_snapshot_with_hooks(&input, READ_CHUNK_BYTES * 3, &mut hooks);
        match result {
            Ok(_) => panic!("{mutation}: mutation must be detected"),
            Err(error) => {
                assert_eq!(error.code(), AdapterErrorCodeV0::InputChanged, "{mutation}")
            }
        }
        assert_eq!(calls.get(), 1, "{mutation}");
        fs::remove_dir_all(root).unwrap();
    }
}

#[test]
fn cap_plus_one_sparse_and_growth_precedence_are_exact() {
    let _guard = filesystem_test_guard();
    let root = temp_directory("caps");
    let exact = root.join("exact");
    fs::write(&exact, vec![b'e'; READ_CHUNK_BYTES]).unwrap();
    assert_eq!(
        read_snapshot(&exact, READ_CHUNK_BYTES).unwrap().bytes.len(),
        READ_CHUNK_BYTES
    );

    let over = root.join("over");
    fs::write(&over, vec![b'o'; READ_CHUNK_BYTES + 1]).unwrap();
    let over_calls = Rc::new(Cell::new(0));
    let over_calls_in_hook = Rc::clone(&over_calls);
    let mut over_hooks = TestHooks {
        first_chunk: Box::new(move || over_calls_in_hook.set(over_calls_in_hook.get() + 1)),
        ..TestHooks::default()
    };
    assert_code(
        read_snapshot_with_hooks(&over, READ_CHUNK_BYTES, &mut over_hooks),
        AdapterErrorCodeV0::InputTooLarge,
    );
    assert_eq!(over_calls.get(), 1);

    let sparse = root.join("sparse");
    fs::File::create(&sparse)
        .unwrap()
        .set_len((READ_CHUNK_BYTES + 1) as u64)
        .unwrap();
    assert_code(
        read_snapshot(&sparse, READ_CHUNK_BYTES),
        AdapterErrorCodeV0::InputTooLarge,
    );

    let growing = root.join("growing");
    fs::write(&growing, vec![b'g'; READ_CHUNK_BYTES]).unwrap();
    let growing_in_hook = growing.clone();
    let growth_calls = Rc::new(Cell::new(0));
    let growth_calls_in_hook = Rc::clone(&growth_calls);
    let mut growth_hooks = TestHooks {
        first_chunk: Box::new(move || {
            growth_calls_in_hook.set(growth_calls_in_hook.get() + 1);
            fs::OpenOptions::new()
                .append(true)
                .open(&growing_in_hook)
                .unwrap()
                .write_all(b"!")
                .unwrap();
        }),
        ..TestHooks::default()
    };
    assert_code(
        read_snapshot_with_hooks(&growing, READ_CHUNK_BYTES, &mut growth_hooks),
        AdapterErrorCodeV0::InputChanged,
    );
    assert_eq!(growth_calls.get(), 1);
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn authority_sized_reads_use_the_cap_plus_one_staging_allocation() {
    let _guard = filesystem_test_guard();
    let root = temp_directory("authority-staging");
    let input = root.join("input");
    let bytes = [0x5a_u8; 32];
    fs::write(&input, bytes).unwrap();
    let observed = Rc::new(Cell::new(None));
    let observed_in_hook = Rc::clone(&observed);
    let mut hooks = TestHooks {
        staging_read: Box::new(move |staging, read| {
            observed_in_hook.set(Some((staging.len(), read, staging[..read] == bytes)));
        }),
        ..TestHooks::default()
    };
    let snapshot = read_snapshot_with_hooks(&input, 32, &mut hooks).unwrap();
    assert_eq!(snapshot.bytes.as_slice(), bytes);
    assert_eq!(observed.get(), Some((33, 32, true)));
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn all_three_hard_link_input_pairs_are_rejected() {
    let _guard = filesystem_test_guard();
    for pair in [(0, 1), (0, 2), (1, 2)] {
        let root = temp_directory(&format!("aliases-{}-{}", pair.0, pair.1));
        let paths = [root.join("raw"), root.join("receipt"), root.join("context")];
        for path in &paths {
            fs::write(path, b"x").unwrap();
        }
        fs::remove_file(&paths[pair.1]).unwrap();
        fs::hard_link(&paths[pair.0], &paths[pair.1]).unwrap();
        let snapshots = paths
            .iter()
            .map(|path| read_snapshot(path, 8).unwrap())
            .collect::<Vec<_>>();
        assert_code(
            reject_duplicate_inodes(&[&snapshots[0], &snapshots[1], &snapshots[2]]),
            AdapterErrorCodeV0::InputAlias,
        );
        fs::remove_dir_all(root).unwrap();
    }
}

#[test]
fn procfs_profile_gate_reader_identity_and_flags_are_asserted() {
    let _guard = filesystem_test_guard();
    let root = temp_directory("proc-profile");
    let input = root.join("input");
    fs::write(&input, b"stable").unwrap();
    assert_snapshot(&input, 8, b"stable");

    let mut wrong_proc = TestHooks {
        proc_root: Some(root.clone()),
        ..TestHooks::default()
    };
    assert_code(
        read_snapshot_with_hooks(&input, 8, &mut wrong_proc),
        AdapterErrorCodeV0::UnsupportedInputProfile,
    );
    let missing_proc = root.join("missing-proc");
    let mut missing_proc_hooks = TestHooks {
        proc_root: Some(missing_proc),
        ..TestHooks::default()
    };
    assert_code(
        read_snapshot_with_hooks(&input, 8, &mut missing_proc_hooks),
        AdapterErrorCodeV0::UnsupportedInputProfile,
    );
    let proc_symlink = root.join("proc-symlink");
    symlink("/proc", &proc_symlink).unwrap();
    let mut proc_symlink_hooks = TestHooks {
        proc_root: Some(proc_symlink),
        ..TestHooks::default()
    };
    assert_code(
        read_snapshot_with_hooks(&input, 8, &mut proc_symlink_hooks),
        AdapterErrorCodeV0::UnsupportedInputProfile,
    );
    let input_for_probe = input.clone();
    let probe_calls = Rc::new(Cell::new(0));
    let probe_calls_in_hook = Rc::clone(&probe_calls);
    let mut mutation_before_profile_failure = TestHooks {
        proc_root: Some(root.clone()),
        proc_probe: Some(Box::new(move || {
            probe_calls_in_hook.set(probe_calls_in_hook.get() + 1);
            let mut permissions = fs::metadata(&input_for_probe).unwrap().permissions();
            permissions.set_mode(0o400);
            fs::set_permissions(&input_for_probe, permissions).unwrap();
        })),
        ..TestHooks::default()
    };
    assert_code(
        read_snapshot_with_hooks(&input, 8, &mut mutation_before_profile_failure),
        AdapterErrorCodeV0::InputChanged,
    );
    assert_eq!(probe_calls.get(), 1);
    let mut permissions = fs::metadata(&input).unwrap().permissions();
    permissions.set_mode(0o600);
    fs::set_permissions(&input, permissions).unwrap();

    let gate = openat(
        rustix::fs::CWD,
        &input,
        OFlags::PATH | OFlags::NOFOLLOW | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .unwrap();
    let baseline = fingerprint(&fstat(&gate).unwrap());
    let valid = openat(
        rustix::fs::CWD,
        &input,
        OFlags::RDONLY | OFlags::NONBLOCK | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .unwrap();
    validate_reader(&valid, baseline).unwrap();
    assert_code(
        validate_reader(&gate, baseline),
        AdapterErrorCodeV0::UnsupportedInputProfile,
    );

    let other = root.join("other");
    fs::write(&other, b"stable").unwrap();
    let wrong_inode = openat(
        rustix::fs::CWD,
        &other,
        OFlags::RDONLY | OFlags::NONBLOCK | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .unwrap();
    assert_code(
        validate_reader(&wrong_inode, baseline),
        AdapterErrorCodeV0::UnsupportedInputProfile,
    );

    let missing_nonblock = openat(
        rustix::fs::CWD,
        &input,
        OFlags::RDONLY | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .unwrap();
    assert_code(
        validate_reader(&missing_nonblock, baseline),
        AdapterErrorCodeV0::UnsupportedInputProfile,
    );
    let wrong_access = openat(
        rustix::fs::CWD,
        &input,
        OFlags::WRONLY | OFlags::NONBLOCK | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .unwrap();
    assert_code(
        validate_reader(&wrong_access, baseline),
        AdapterErrorCodeV0::UnsupportedInputProfile,
    );
    let missing_cloexec = openat(
        rustix::fs::CWD,
        &input,
        OFlags::RDONLY | OFlags::NONBLOCK | OFlags::CLOEXEC,
        Mode::empty(),
    )
    .unwrap();
    fcntl_setfd(&missing_cloexec, FdFlags::empty()).unwrap();
    assert_code(
        validate_reader(&missing_cloexec, baseline),
        AdapterErrorCodeV0::UnsupportedInputProfile,
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn fifo_preopen_swap_is_bounded_in_a_killable_subprocess() {
    let _guard = filesystem_test_guard();
    const CHILD_ENV: &str = "LEGITIMACY_LINUX_FIFO_SWAP_CHILD";
    const MARKER_ENV: &str = "LEGITIMACY_LINUX_FIFO_SWAP_MARKER";
    if let Some(marker) = std::env::var_os(MARKER_ENV) {
        assert!(std::env::var_os(CHILD_ENV).is_some());
        let initial_root = temp_directory("fifo-initial-child");
        let initial_fifo = initial_root.join("fifo");
        mkfifo(&initial_fifo);
        assert_code(
            read_snapshot(&initial_fifo, 8),
            AdapterErrorCodeV0::InputType,
        );
        fs::remove_dir_all(initial_root).unwrap();

        let root = temp_directory("fifo-swap-child");
        let input = root.join("input");
        let moved = root.join("moved");
        fs::write(&input, b"regular").unwrap();
        let input_in_hook = input.clone();
        let mut hooks = TestHooks {
            final_open: Box::new(move || {
                fs::rename(&input_in_hook, &moved).unwrap();
                mkfifo(&input_in_hook);
            }),
            ..TestHooks::default()
        };
        assert_code(
            read_snapshot_with_hooks(&input, 8, &mut hooks),
            AdapterErrorCodeV0::InputChanged,
        );
        fs::remove_dir_all(root).unwrap();
        fs::write(marker, b"both-fifo-assertions-passed").unwrap();
        return;
    }

    let test_name =
        "trajectory::linux_path::tests::fifo_preopen_swap_is_bounded_in_a_killable_subprocess";
    let marker_root = temp_directory("fifo-marker");
    let marker = marker_root.join("passed");
    let mut child = std::process::Command::new(std::env::current_exe().unwrap())
        .args([test_name, "--exact"])
        .env(CHILD_ENV, "1")
        .env(MARKER_ENV, &marker)
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .spawn()
        .unwrap();
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
    loop {
        if let Some(status) = child.try_wait().unwrap() {
            assert!(status.success(), "FIFO seam child failed: {status}");
            break;
        }
        if std::time::Instant::now() >= deadline {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!("FIFO seam child exceeded the five-second deadline");
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
    assert_eq!(
        fs::read(&marker).unwrap(),
        b"both-fifo-assertions-passed",
        "child must prove both FIFO assertions ran"
    );
    fs::remove_dir_all(marker_root).unwrap();
}

#[test]
fn snapshot_buffer_zeroizes_on_panic_unwind() {
    const FINDING: &[u8] = b"AUTHORITY_KEY_REMANENCE: marker reached free without clearing\n";
    const CHILD_ENV: &str = "LEGITIMACY_KEY_UNWIND_PROBE_PATH";
    let _guard = filesystem_test_guard();
    let root = temp_directory("zeroize-unwind");
    let probe = root.join("key-free-probe.so");
    let compiler = std::process::Command::new("cc")
        .args(["-shared", "-fPIC", "-O2", "-Wall", "-Wextra", "-Werror"])
        .arg(
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("tests/fixtures/trajectory-replay-v0/key_free_probe.c"),
        )
        .arg("-o")
        .arg(&probe)
        .output()
        .unwrap();
    assert!(compiler.status.success(), "{compiler:?}");
    assert!(compiler.stdout.is_empty(), "{compiler:?}");
    assert!(compiler.stderr.is_empty(), "{compiler:?}");

    let key = root.join("authority.key");
    fs::write(
        &key,
        [
            0x91, 0x02, 0xa3, 0x14, 0xb5, 0x26, 0xc7, 0x38, 0xd9, 0x4a, 0xeb, 0x5c, 0xfd, 0x6e,
            0x8f, 0x70, 0x81, 0xf2, 0x63, 0xd4, 0x45, 0xb6, 0x27, 0x98, 0x09, 0x7a, 0xcb, 0x3c,
            0xad, 0x1e, 0xef, 0x50,
        ],
    )
    .unwrap();
    let child = std::process::Command::new(std::env::current_exe().unwrap())
        .args([
            "trajectory::linux_path::tests::snapshot_buffer_zeroizes_on_panic_unwind_child",
            "--exact",
            "--ignored",
        ])
        .env(CHILD_ENV, &key)
        .env("LD_PRELOAD", &probe)
        .output()
        .unwrap();
    assert!(!child.status.success(), "{child:?}");
    assert!(
        !child
            .stderr
            .windows(FINDING.len())
            .any(|window| window == FINDING),
        "{child:?}"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
#[ignore = "invoked by snapshot_buffer_zeroizes_on_panic_unwind"]
fn snapshot_buffer_zeroizes_on_panic_unwind_child() {
    let Some(path) = std::env::var_os("LEGITIMACY_KEY_UNWIND_PROBE_PATH") else {
        return;
    };
    let snapshot = read_snapshot(Path::new(&path), 32).unwrap();
    assert_eq!(snapshot.bytes.len(), 32);
    panic!("intentional panic-unwind key-remanence probe");
}

fn assert_snapshot(path: &Path, cap: usize, expected: &[u8]) {
    let snapshot = read_snapshot(path, cap).unwrap();
    assert_eq!(snapshot.bytes.as_slice(), expected);
}

fn assert_code<T>(result: Result<T, AdapterErrorV0>, expected: AdapterErrorCodeV0) {
    match result {
        Ok(_) => panic!("expected {}", expected.as_str()),
        Err(error) => assert_eq!(error.code(), expected),
    }
}

fn mkfifo(path: &Path) {
    assert!(
        std::process::Command::new("mkfifo")
            .arg(path)
            .status()
            .unwrap()
            .success()
    );
}

fn temp_directory(label: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "legitimacy-linux-path-{}-{label}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&path).unwrap();
    path
}

fn filesystem_test_guard() -> MutexGuard<'static, ()> {
    FILESYSTEM_TEST_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}
