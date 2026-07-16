use std::{fs, path::Path};

const MAX_LINES: usize = 1000;

#[test]
fn rust_source_files_stay_under_the_file_cap() {
    for root in ["src", "cli"] {
        assert_file_cap(Path::new(root));
    }
}

fn assert_file_cap(path: &Path) {
    if path.is_dir() {
        for entry in fs::read_dir(path).expect("source directory should be readable") {
            let entry = entry.expect("directory entry should be readable");
            assert_file_cap(&entry.path());
        }
        return;
    }

    if path.extension().and_then(|ext| ext.to_str()) != Some("rs") {
        return;
    }

    let line_count = fs::read_to_string(path)
        .expect("source file should be readable")
        .lines()
        .count();

    assert!(
        line_count <= MAX_LINES,
        "{} has {} lines, exceeding the {} line cap",
        path.display(),
        line_count,
        MAX_LINES
    );
}
