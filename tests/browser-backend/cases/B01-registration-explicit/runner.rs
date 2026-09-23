// Ported from the BL-003 spike's collector runner: the registrations
// come from an explicit table instead of `inventory::iter`; everything else,
// including the output schema and the COLLECTOR_* controls, is unchanged.
use b01_model::Registration;
use std::any::TypeId;
use std::env;
use std::fmt::Write as _;
use std::fs;
use std::io::{self, Write as _};
use std::path::{Path, PathBuf};

const SUCCESS_SCHEMA: &str = "krs.browser-lessons.collector-primitives.v1";
const ERROR_SCHEMA: &str = "krs.browser-lessons.collector-error.v1";

struct ObservedRegistration {
    name: &'static str,
    ordinal: u32,
    rendered: String,
    type_id_equal: bool,
    type_id_unequal: bool,
}

pub fn run(table: &[&'static Registration]) -> Result<String, Failure> {
    match env::var("COLLECTOR_MODE").as_deref() {
        Ok("trap") => panic!("deliberate BL-003 trap"),
        Ok("spin") => loop {
            std::hint::spin_loop();
        },
        _ => {}
    }

    let manifest = absolute_env_path("COLLECTOR_MANIFEST_PATH", "/workspace/Cargo.toml")?;
    let source = absolute_env_path("COLLECTOR_SOURCE_PATH", "/workspace/src/lesson.krs")?;
    let manifest = canonicalize("manifest_canonicalize", &manifest)?;
    let source = canonicalize("source_canonicalize", &source)?;
    let manifest_text = read_text("manifest_read", &manifest)?;
    let source_text = read_text("source_read", &source)?;

    let mut registrations = table
        .iter()
        .map(|registration| {
            let value = (registration.factory)();
            let actual_type_id = value.as_ref().type_id();
            let expected_type_id = (registration.expected_type_id)();
            let rendered = (registration.render)(value.as_ref()).map_err(|message| Failure {
                stage: "registration_render",
                path: None,
                kind: "TypeMismatch".to_owned(),
                message: message.to_owned(),
            })?;
            Ok(ObservedRegistration {
                name: registration.name,
                ordinal: registration.ordinal,
                rendered,
                type_id_equal: actual_type_id == expected_type_id,
                type_id_unequal: actual_type_id != TypeId::of::<bool>(),
            })
        })
        .collect::<Result<Vec<_>, Failure>>()?;
    registrations.sort_by_key(|registration| (registration.name, registration.ordinal));

    let mut linked_inputs: Vec<&str> = table.iter().map(|registration| registration.name).collect();
    linked_inputs.sort_unstable();

    let mut output = String::new();
    output.push_str("{\"linked_inputs\":[");
    for (index, input) in linked_inputs.iter().enumerate() {
        if index != 0 {
            output.push(',');
        }
        push_json_string(&mut output, input);
    }
    output.push_str("],\"manifest\":{\"path\":");
    push_json_string(&mut output, &manifest.display().to_string());
    output.push_str(",\"text\":");
    push_json_string(&mut output, &manifest_text);
    output.push_str("},\"registrations\":[");
    for (index, registration) in registrations.iter().enumerate() {
        if index != 0 {
            output.push(',');
        }
        output.push_str("{\"name\":");
        push_json_string(&mut output, registration.name);
        write!(output, ",\"ordinal\":{}", registration.ordinal).expect("write String");
        output.push_str(",\"rendered\":");
        push_json_string(&mut output, &registration.rendered);
        write!(
            output,
            ",\"type_id_equal\":{},\"type_id_unequal\":{}}}",
            registration.type_id_equal, registration.type_id_unequal,
        )
        .expect("write String");
    }
    output.push_str("],\"schema\":");
    push_json_string(&mut output, SUCCESS_SCHEMA);
    output.push_str(",\"source\":{\"path\":");
    push_json_string(&mut output, &source.display().to_string());
    output.push_str(",\"text\":");
    push_json_string(&mut output, &source_text);
    write!(
        output,
        "}},\"type_id_control\":{{\"equal\":{},\"unequal\":{}}}}}",
        TypeId::of::<u32>() == TypeId::of::<u32>(),
        TypeId::of::<u32>() != TypeId::of::<String>(),
    )
    .expect("write String");
    Ok(output)
}

pub fn main_with_registrations(table: &[&'static Registration]) {
    match run(table) {
        Ok(output) => println!("{output}"),
        Err(failure) => {
            let _ = writeln!(io::stderr(), "{}", failure.as_json());
            std::process::exit(2);
        }
    }
}

fn push_json_string(output: &mut String, value: &str) {
    output.push('"');
    for character in value.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            character if character <= '\u{1f}' => {
                write!(output, "\\u{:04x}", u32::from(character)).expect("write String");
            }
            character => output.push(character),
        }
    }
    output.push('"');
}

fn absolute_env_path(name: &'static str, default: &'static str) -> Result<PathBuf, Failure> {
    let value = env::var_os(name)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(default));
    if value.is_absolute() {
        Ok(value)
    } else {
        Err(Failure {
            stage: "input_validation",
            path: Some(value),
            kind: "RelativePath".to_owned(),
            message: format!("{name} must be an absolute guest path"),
        })
    }
}

fn canonicalize(stage: &'static str, path: &Path) -> Result<PathBuf, Failure> {
    fs::canonicalize(path).map_err(|error| Failure::io(stage, path, error))
}

fn read_text(stage: &'static str, path: &Path) -> Result<String, Failure> {
    fs::read_to_string(path).map_err(|error| Failure::io(stage, path, error))
}

pub struct Failure {
    stage: &'static str,
    path: Option<PathBuf>,
    kind: String,
    message: String,
}

impl Failure {
    fn io(stage: &'static str, path: &Path, error: io::Error) -> Self {
        Self {
            stage,
            path: Some(path.to_owned()),
            kind: format!("{:?}", error.kind()),
            message: error.to_string(),
        }
    }

    fn as_json(&self) -> String {
        let mut output = String::from("{\"error\":{\"kind\":");
        push_json_string(&mut output, &self.kind);
        output.push_str(",\"message\":");
        push_json_string(&mut output, &self.message);
        output.push_str(",\"path\":");
        match &self.path {
            Some(path) => push_json_string(&mut output, &path.display().to_string()),
            None => output.push_str("null"),
        }
        output.push_str(",\"stage\":");
        push_json_string(&mut output, self.stage);
        output.push_str("},\"schema\":");
        push_json_string(&mut output, ERROR_SCHEMA);
        output.push('}');
        output
    }
}
