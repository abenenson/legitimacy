use std::process::ExitCode;

fn main() -> ExitCode {
    if !bounded_path("src/")
        || bounded_path("src//")
        || bounded_path("../src/")
        || bounded_path("/src/")
        || bounded_path("src/./")
        || bounded_path("src\\")
    {
        eprintln!("selected Git answer: invalid path protocol");
        return ExitCode::FAILURE;
    }
    match answer(std::env::args().skip(1).collect()) {
        Ok(output) => {
            print!("{output}");
            ExitCode::SUCCESS
        }
        Err(message) => {
            eprintln!("selected Git answer: {message}");
            ExitCode::FAILURE
        }
    }
}

fn answer(arguments: Vec<String>) -> Result<String, &'static str> {
    match arguments.as_slice() {
        [command, format, head]
            if command == "rev-parse" && format == "--short=7" && head == "HEAD" =>
        {
            exact_environment("LEGITIMACY_GIT_ANSWER_SHORT")
        }
        [command, porcelain, separator, path]
            if command == "status"
                && porcelain == "--porcelain"
                && separator == "--"
                && bounded_path(path) =>
        {
            status_answer(path)
        }
        [command, count, format, separator, path]
            if command == "log"
                && count == "-n"
                && format == "1"
                && separator == "--format=%H" =>
        {
            let _ = path;
            Err("malformed log argv")
        }
        [command, count, one, format, separator, path]
            if command == "log"
                && count == "-n"
                && one == "1"
                && format == "--format=%H"
                && separator == "--"
                && bounded_path(path) =>
        {
            commit_answer(path)
        }
        _ => Err("unsupported argv"),
    }
}

fn status_answer(path: &str) -> Result<String, &'static str> {
    let declared = exact_environment("LEGITIMACY_GIT_ANSWER_DIRTY_PATHS")?;
    if declared.lines().any(|candidate| candidate == path) {
        Ok(format!(" M {path}\n"))
    } else {
        Ok(String::new())
    }
}

fn commit_answer(path: &str) -> Result<String, &'static str> {
    let table = exact_environment("LEGITIMACY_GIT_ANSWER_COMMITS")?;
    let matches = table
        .lines()
        .filter_map(|line| line.split_once('\t'))
        .filter(|(candidate, _)| *candidate == path)
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [(_, commit)]
            if commit.len() == 40
                && commit
                    .bytes()
                    .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)) =>
        {
            Ok(format!("{commit}\n"))
        }
        _ => Err("undeclared fixture"),
    }
}

fn exact_environment(name: &str) -> Result<String, &'static str> {
    std::env::var(name).map_err(|_| "missing answer environment")
}

fn bounded_path(path: &str) -> bool {
    let path = path.strip_suffix('/').unwrap_or(path);
    !path.is_empty()
        && path.len() <= 4096
        && !path.contains('\0')
        && !path.contains('\\')
        && !path.starts_with('/')
        && path
            .split('/')
            .all(|component| !component.is_empty() && component != "." && component != "..")
}
