//! The user guide for `kink-flow fuzz` and `krust fuzz`, k-rust's `docs/fuzzing.md` (fz26
//! FZ-GUIDE), runs as written.
//!
//! The guide's fenced blocks take four forms, which the light test checks:
//! - `sh`: commands. The kink-tier test runs the blocks that use `kink-flow` (and blocks that use
//!   no tool), in order; k-rust-fuzz's `tests/cli.rs` runs the blocks that use `krust`. A line is
//!   `cp -r SOURCE DIRECTORY`, `cd DIRECTORY`, `cat > FILE <<'EOF'` or `cat >> FILE <<'EOF'` with
//!   the file's lines up to a line `EOF`, or a command with an optional `> FILE` and an optional
//!   trailing `# exit N` (exit status 0 otherwise). A relative SOURCE names a path of the
//!   repository; a path under `/tmp/` names one under the test's scratch directory, so nothing is
//!   written into the repository. Single quotes group a word.
//! - `json`, directly after an `sh` block: contained in the JSON document the block's last command
//!   printed. An object's members are a subset of the document's, an array's elements match
//!   distinct elements of the document's array in order, a string that starts or ends with `…`
//!   matches by the text it shows (a prefix, a suffix or a part), and any other value is equal.
//! - `text`, directly after an `sh` block: each line is a line of the last command's output, in
//!   order.
//! - a block titled with a repository path (`toml [kink/testdata/...]`, the docs site's title
//!   syntax): its lines are consecutive lines of that file.
//!
//! The commands run on the flows `testdata/flow/fuzz/imp` and `impu` with small budgets and the
//! default seed, so the stated outcomes are deterministic.

use serde_json::Value;
use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Stdio},
};

/// The root of k-rust's repository, which holds `docs/fuzzing.md` and `kink/`.
fn repository() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..")
}

fn guide() -> String {
    fs::read_to_string(repository().join("docs/fuzzing.md")).expect("docs/fuzzing.md is readable")
}

/// A fenced block of the guide: its language, its title (`[PATH]`), its lines and the line of
/// its opening fence (1-based).
#[derive(Debug)]
struct Block {
    language: String,
    title: Option<String>,
    lines: Vec<String>,
    line: usize,
}

fn blocks(text: &str) -> Vec<Block> {
    let mut blocks = Vec::new();
    let mut open: Option<Block> = None;
    for (index, line) in text.lines().enumerate() {
        let Some(info) = line.strip_prefix("```") else {
            if let Some(block) = open.as_mut() {
                block.lines.push(line.to_owned());
            }
            continue;
        };
        match open.take() {
            Some(block) => {
                assert!(
                    info.is_empty(),
                    "line {}: a fence inside a block",
                    index + 1
                );
                blocks.push(block);
            }
            None => {
                let (language, title) = match info.split_once(' ') {
                    Some((language, title)) => {
                        let title = title
                            .strip_prefix('[')
                            .and_then(|title| title.strip_suffix(']'))
                            .unwrap_or_else(|| panic!("line {}: a title is `[PATH]`", index + 1));
                        (language, Some(title.to_owned()))
                    }
                    None => (info, None),
                };
                open = Some(Block {
                    language: language.to_owned(),
                    title,
                    lines: Vec::new(),
                    line: index + 1,
                });
            }
        }
    }
    assert!(open.is_none(), "an unclosed block");
    blocks
}

/// A word of a command line, and whether it was quoted (a quoted `>` is no redirection).
type Word = (String, bool);

/// The words of `line`, and the exit status its trailing `# exit N` comment states.
fn words(line: &str) -> (Vec<Word>, Option<i32>) {
    let mut words = Vec::new();
    let mut rest = line.trim_start();
    while !rest.is_empty() {
        if let Some(comment) = rest.strip_prefix('#') {
            let status = comment.trim().strip_prefix("exit ").map(|status| {
                status
                    .trim()
                    .parse()
                    .unwrap_or_else(|_| panic!("`{line}`: `# exit N` takes a number"))
            });
            return (words, status);
        }
        if let Some(quoted) = rest.strip_prefix('\'') {
            let end = quoted
                .find('\'')
                .unwrap_or_else(|| panic!("`{line}`: an unclosed quote"));
            words.push((quoted[..end].to_owned(), true));
            rest = quoted[end + 1..].trim_start();
        } else {
            let end = rest.find(char::is_whitespace).unwrap_or(rest.len());
            words.push((rest[..end].to_owned(), false));
            rest = rest[end..].trim_start();
        }
    }
    (words, None)
}

/// One step of an `sh` block.
#[derive(Debug)]
enum Step {
    Copy(String, String),
    Cd(String),
    Write {
        file: String,
        append: bool,
        lines: Vec<String>,
    },
    Run {
        args: Vec<String>,
        output: Option<String>,
        status: i32,
    },
}

/// The steps of an `sh` block, or the reason a line is not one of the guide's forms.
fn steps(block: &Block) -> Result<Vec<Step>, String> {
    let mut steps = Vec::new();
    let mut lines = block.lines.iter();
    while let Some(line) = lines.next() {
        let (words, status) = words(line);
        let plain = words
            .iter()
            .map(|(word, _)| word.as_str())
            .collect::<Vec<_>>();
        match plain.as_slice() {
            [] => {}
            ["cp", "-r", source, target] => {
                steps.push(Step::Copy((*source).to_owned(), (*target).to_owned()));
            }
            ["cd", directory] => steps.push(Step::Cd((*directory).to_owned())),
            ["cat", redirect @ (">" | ">>"), file, "<<'EOF'"] => {
                let mut body = Vec::new();
                loop {
                    match lines.next() {
                        Some(line) if line == "EOF" => break,
                        Some(line) => body.push(line.clone()),
                        None => return Err(format!("`{line}`: no line `EOF`")),
                    }
                }
                steps.push(Step::Write {
                    file: (*file).to_owned(),
                    append: *redirect == ">>",
                    lines: body,
                });
            }
            [tool, ..] if *tool == "kink-flow" || *tool == "krust" => {
                let mut args = Vec::new();
                let mut output = None;
                let mut iter = words.iter();
                while let Some((word, quoted)) = iter.next() {
                    if word == ">" && !quoted {
                        let (file, _) = iter
                            .next()
                            .ok_or_else(|| format!("`{line}`: `>` names no file"))?;
                        output = Some(file.clone());
                    } else if word.starts_with('>') && !quoted {
                        return Err(format!("`{line}`: only `> FILE` redirects"));
                    } else {
                        args.push(word.clone());
                    }
                }
                steps.push(Step::Run {
                    args,
                    output,
                    status: status.unwrap_or(0),
                });
            }
            _ => return Err(format!("`{line}` is none of the guide's forms")),
        }
    }
    Ok(steps)
}

/// The tools an `sh` block runs.
fn tools(steps: &[Step]) -> Vec<&str> {
    let mut tools = steps
        .iter()
        .filter_map(|step| match step {
            Step::Run { args, .. } => Some(args[0].as_str()),
            _ => None,
        })
        .collect::<Vec<_>>();
    tools.sort_unstable();
    tools.dedup();
    tools
}

/// Whether `excerpt` (a string of the guide) shows `actual`: equal, or by the part between its
/// leading and trailing `…`.
fn shows(excerpt: &str, actual: &str) -> bool {
    let core = excerpt.trim_start_matches('…').trim_end_matches('…');
    match (excerpt.starts_with('…'), excerpt.ends_with('…')) {
        (false, false) => actual == excerpt,
        (true, true) => actual.contains(core),
        (true, false) => actual.ends_with(core),
        (false, true) => actual.starts_with(core),
    }
}

/// Whether `document` contains `excerpt` at `path` (module documentation), or where not.
fn contains(document: &Value, excerpt: &Value, path: &str) -> Result<(), String> {
    match (excerpt, document) {
        (Value::Object(excerpt), Value::Object(document)) => {
            for (key, value) in excerpt {
                let path = format!("{path}.{key}");
                let found = document.get(key).ok_or_else(|| format!("{path}: absent"))?;
                contains(found, value, &path)?;
            }
            Ok(())
        }
        (Value::Array(excerpt), Value::Array(document)) => {
            let mut next = 0;
            for (index, value) in excerpt.iter().enumerate() {
                let mut last = None;
                loop {
                    let Some(candidate) = document.get(next) else {
                        return Err(last.unwrap_or_else(|| {
                            format!("{path}[{index}]: no element left to match")
                        }));
                    };
                    next += 1;
                    match contains(candidate, value, &format!("{path}[{}]", next - 1)) {
                        Ok(()) => break,
                        Err(error) => last = Some(error),
                    }
                }
            }
            Ok(())
        }
        (Value::String(excerpt), Value::String(actual)) if shows(excerpt, actual) => Ok(()),
        _ if excerpt == document => Ok(()),
        _ => Err(format!(
            "{path}: the guide shows {excerpt}, the command gave {document}"
        )),
    }
}

/// Copy the directory `from` to `to`, recursively.
fn copy_directory(from: &Path, to: &Path) {
    fs::create_dir_all(to).unwrap();
    for entry in fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let target = to.join(entry.file_name());
        if entry.file_type().unwrap().is_dir() {
            copy_directory(&entry.path(), &target);
        } else {
            fs::copy(entry.path(), target).unwrap();
        }
    }
}

/// How a command runs: its words and its directory give its exit status and standard output.
type Runner<'a> = &'a dyn Fn(&[String], &Path) -> (i32, String);

/// The state of a run of the guide's commands: the scratch directory standing for `/tmp`, the
/// current directory, and the last command's output.
struct Session {
    scratch: PathBuf,
    cwd: PathBuf,
    stdout: String,
}

impl Session {
    fn new(name: &str) -> Self {
        let scratch = Path::new(env!("CARGO_TARGET_TMPDIR"))
            .join("guide")
            .join(name);
        let _ = fs::remove_dir_all(&scratch);
        fs::create_dir_all(&scratch).unwrap();
        Self {
            cwd: repository(),
            scratch,
            stdout: String::new(),
        }
    }

    /// The file `word` names: under the scratch directory for `/tmp/...`, else in the current
    /// directory, which must be under the scratch directory.
    fn path(&self, word: &str) -> PathBuf {
        let path = match word.strip_prefix("/tmp/") {
            Some(rest) => self.scratch.join(rest),
            None if Path::new(word).is_absolute() => panic!("`{word}`: only /tmp paths"),
            None => self.cwd.join(word),
        };
        assert!(
            path.starts_with(&self.scratch),
            "`{word}` names a file outside the scratch directory; `cd` into /tmp first"
        );
        path
    }

    /// Run `steps`, each command through `run` (its arguments and directory give its exit status
    /// and standard output).
    fn run(&mut self, block: &Block, steps: &[Step], run: Runner<'_>) {
        for step in steps {
            match step {
                Step::Copy(source, target) => {
                    assert!(
                        !Path::new(source).is_absolute(),
                        "`cp` copies from the repository"
                    );
                    copy_directory(&repository().join(source), &self.path(target));
                }
                Step::Cd(directory) => {
                    let directory = self.path(directory);
                    assert!(
                        directory.is_dir(),
                        "{} is no directory",
                        directory.display()
                    );
                    self.cwd = directory;
                }
                Step::Write {
                    file,
                    append,
                    lines,
                } => {
                    let path = self.path(file);
                    let mut text = if *append {
                        fs::read_to_string(&path).unwrap()
                    } else {
                        String::new()
                    };
                    for line in lines {
                        text.push_str(line);
                        text.push('\n');
                    }
                    fs::write(path, text).unwrap();
                }
                Step::Run {
                    args,
                    output,
                    status,
                } => {
                    assert!(
                        self.cwd.starts_with(&self.scratch),
                        "line {}: `cd` into /tmp before running a command",
                        block.line
                    );
                    let (code, stdout) = run(args, &self.cwd);
                    assert_eq!(
                        code,
                        *status,
                        "guide line {}: `{}` exited {code}; stdout: {stdout}",
                        block.line,
                        args.join(" ")
                    );
                    if let Some(file) = output {
                        fs::write(self.path(file), &stdout).unwrap();
                    }
                    self.stdout = stdout;
                }
            }
        }
    }

    /// Check the output excerpt `block` against the last command's output.
    fn check(&self, block: &Block) {
        let excerpt = block.lines.join("\n");
        match block.language.as_str() {
            "json" => {
                let excerpt: Value = serde_json::from_str(&excerpt)
                    .unwrap_or_else(|e| panic!("guide line {}: not JSON: {e}", block.line));
                let document: Value = serde_json::from_str(&self.stdout)
                    .unwrap_or_else(|e| panic!("guide line {}: no document: {e}", block.line));
                if let Err(difference) = contains(&document, &excerpt, "") {
                    panic!("guide line {}: {difference}", block.line);
                }
            }
            "text" => {
                let mut lines = self.stdout.lines();
                for line in &block.lines {
                    assert!(
                        lines.any(|output| output == line),
                        "guide line {}: `{line}` is not in the output (in order):\n{}",
                        block.line,
                        self.stdout
                    );
                }
            }
            other => panic!("guide line {}: no excerpt of language {other}", block.line),
        }
    }
}

/// Every block of the guide is one of its forms, every `sh` block is the commands of one tool,
/// and every block titled with a file quotes consecutive lines of it.
#[test]
fn the_guide_blocks_are_commands_outputs_or_quoted_files() {
    let blocks = blocks(&guide());
    let mut previous_sh = false;
    let mut counts = [0; 2];
    for block in &blocks {
        if let Some(title) = &block.title {
            let file = fs::read_to_string(repository().join(title))
                .unwrap_or_else(|e| panic!("guide line {}: {title}: {e}", block.line));
            let file = file.lines().collect::<Vec<_>>();
            let quoted = block.lines.iter().map(String::as_str).collect::<Vec<_>>();
            assert!(
                file.windows(quoted.len()).any(|window| window == quoted),
                "guide line {}: the block does not quote consecutive lines of {title}",
                block.line
            );
            previous_sh = false;
            continue;
        }
        match block.language.as_str() {
            "sh" => {
                let steps =
                    steps(block).unwrap_or_else(|e| panic!("guide line {}: {e}", block.line));
                let tools = tools(&steps);
                assert!(
                    tools.len() <= 1,
                    "guide line {}: one tool per block",
                    block.line
                );
                match tools.first() {
                    Some(&"kink-flow") => counts[0] += 1,
                    Some(_) => counts[1] += 1,
                    None => {}
                }
                previous_sh = true;
                continue;
            }
            "json" | "text" => assert!(
                previous_sh,
                "guide line {}: an output excerpt follows a command block",
                block.line
            ),
            other => panic!(
                "guide line {}: a `{other}` block is no command, output or quoted file",
                block.line
            ),
        }
        previous_sh = false;
    }
    assert!(counts[0] >= 10 && counts[1] >= 4, "{counts:?}");
}

mod kink_tier {
    use super::*;

    /// Every `kink-flow` command of the guide, in order, gives the exit status and the outcome
    /// fields the guide states.
    #[test]
    #[ignore = "kink"]
    fn the_guide_kink_flow_commands_give_the_stated_outcomes() {
        let blocks = blocks(&guide());
        let mut session = Session::new("kink-flow");
        let run = |args: &[String], directory: &Path| {
            let output = Command::new(env!("CARGO_BIN_EXE_kink-flow"))
                .args(&args[1..])
                .current_dir(directory)
                .stdin(Stdio::null())
                .output()
                .expect("kink-flow runs");
            (
                output.status.code().expect("kink-flow exits"),
                String::from_utf8(output.stdout).expect("UTF-8 output"),
            )
        };
        let mut checked = 0;
        for (index, block) in blocks.iter().enumerate() {
            if block.language != "sh" || block.title.is_some() {
                continue;
            }
            let steps = steps(block).unwrap();
            if tools(&steps).iter().any(|tool| *tool != "kink-flow") {
                continue;
            }
            session.run(block, &steps, &run);
            if let Some(next) = blocks.get(index + 1)
                && next.title.is_none()
                && matches!(next.language.as_str(), "json" | "text")
            {
                session.check(next);
                checked += 1;
            }
        }
        assert!(checked >= 10, "{checked} excerpts checked");
    }
}
