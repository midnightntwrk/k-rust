//! `[[implementation]]`: another implementation of the corpus's system, which `compare` runs on
//! every program and compares with the definition under each of its views ([`crate::compare`]).
//!
//! kink-flow reads the declaration's shape and its own keys (`name`, `command`, `given`,
//! `omits`, `identity`, `time_ms`, each view's `name` and `required`); a view's `compare`,
//! `views` and `observer` are the front end's, which only a front end that reads the
//! definition's values resolves (`crate::compare::Vocabulary::check`). An implementation is no
//! input of the definition's runs, so the declaration is in no digest or cache key.

use super::{
    ManifestError, front_end_key, join, known_keys, missing, names, required_string, table,
};
use toml::{Table, Value};

/// One `[[implementation]]`, as written.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImplementationSection {
    /// `name`: unique among the manifest's implementations.
    pub name: String,
    /// `command`: the argv that runs the implementation on one program, its first word an
    /// executable: a path with a `/` relative to the manifest's directory, else a name the
    /// system looks up on `PATH`.
    pub command: Vec<String>,
    /// `given`: what each request gives the implementation besides the program's inputs.
    pub given: Given,
    /// `omits`: the cells the implementation does not state, by the front end's cell names;
    /// every other cell a view compares must be in its answer.
    pub omits: Vec<String>,
    /// `identity = { file = .. }`: the file whose digest names the implementation's build, for
    /// a later cache of its verdicts; `None`: its verdicts are never cached.
    pub identity: Option<IdentitySection>,
    /// `time_ms`: the wall clock that cancels one run of the implementation; `None`: the
    /// manifest's `budget.time_ms`. It decides no verdict.
    pub time_ms: Option<u64>,
    /// `views`: the views it is compared under, in the order written; at least one.
    pub views: Vec<ViewSection>,
}

/// `given`: what the implementation starts from.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Given {
    /// `"start"`: the definition's start configuration for the program, in the definition's
    /// cell vocabulary, besides the inputs.
    Start,
    /// `"inputs"`: the program's inputs alone.
    Inputs,
}

impl Given {
    /// The value as written.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Start => "start",
            Self::Inputs => "inputs",
        }
    }
}

/// `identity = { file = .. }`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IdentitySection {
    /// `file`: relative to the manifest's directory.
    pub file: String,
}

/// One entry of an implementation's `views`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ViewSection {
    /// `name`: unique among the implementation's views.
    pub name: String,
    /// `required`: only a required view decides `compare`'s exit status; default false, a view
    /// that is reported only.
    pub required: bool,
    /// The front end's keys of the view, as JSON (`compare`, an array of cell names; `views`, a
    /// function by cell; `observer`): which cells are compared, and through which functions of
    /// their values. Empty: every cell the implementation states, as values.
    pub front_end: serde_json::Map<String, serde_json::Value>,
}

impl ImplementationSection {
    /// The declaration as documents name it: `{name, command, given, omits, identity, time_ms,
    /// views: [{name, required, ..front end keys}]}`.
    #[must_use]
    pub fn value(&self) -> serde_json::Value {
        serde_json::json!({
            "name": self.name,
            "command": self.command,
            "given": self.given.as_str(),
            "omits": self.omits,
            "identity": self.identity.as_ref().map(|identity| serde_json::json!({"file": identity.file})),
            "time_ms": self.time_ms,
            "views": self.views.iter().map(ViewSection::value).collect::<Vec<_>>(),
        })
    }

    /// The view named `name`.
    #[must_use]
    pub fn view(&self, name: &str) -> Option<&ViewSection> {
        self.views.iter().find(|view| view.name == name)
    }

    /// Whether some view of the implementation is required.
    #[must_use]
    pub fn has_required_view(&self) -> bool {
        self.views.iter().any(|view| view.required)
    }
}

impl ViewSection {
    /// The view as documents name it: its name, `required`, and the front end's keys.
    #[must_use]
    pub fn value(&self) -> serde_json::Value {
        let mut value = self.front_end.clone();
        value.insert("name".into(), serde_json::json!(self.name));
        value.insert("required".into(), serde_json::json!(self.required));
        serde_json::Value::Object(value)
    }
}

/// The front end's keys of a view ([`ViewSection::front_end`]).
const VIEW_FRONT_END_KEYS: [&str; 3] = ["compare", "views", "observer"];

/// `[[implementation]]`: an array of tables, each name unique.
pub(super) fn implementations(value: &Value) -> Result<Vec<ImplementationSection>, ManifestError> {
    let Value::Array(entries) = value else {
        return Err(ManifestError::new(
            "implementation",
            "expected [[implementation]] tables",
        ));
    };
    let mut implementations = Vec::<ImplementationSection>::new();
    for (index, entry) in entries.iter().enumerate() {
        let prefix = format!("implementation[{index}]");
        let implementation = implementation(table(entry, &prefix)?, &prefix)?;
        if let Some(first) = implementations
            .iter()
            .position(|other| other.name == implementation.name)
        {
            return Err(ManifestError::new(
                join(&prefix, "name"),
                format!(
                    "`{}` is declared twice (implementation[{first}] declares it first)",
                    implementation.name
                ),
            ));
        }
        implementations.push(implementation);
    }
    Ok(implementations)
}

fn implementation(entry: &Table, prefix: &str) -> Result<ImplementationSection, ManifestError> {
    known_keys(
        entry,
        prefix,
        &[
            "name", "command", "given", "omits", "identity", "time_ms", "views",
        ],
    )?;
    let name = nonblank(entry, prefix, "name")?;
    let command_key = join(prefix, "command");
    if !entry.contains_key("command") {
        return Err(missing(&command_key));
    }
    let command = match entry.get("command") {
        Some(Value::Array(words)) if !words.is_empty() => words
            .iter()
            .enumerate()
            .map(|(index, word)| match word {
                Value::String(word) if !word.is_empty() => Ok(word.clone()),
                _ => Err(ManifestError::new(
                    format!("{command_key}[{index}]"),
                    "expected a nonempty string, one word of the command",
                )),
            })
            .collect::<Result<Vec<_>, _>>()?,
        _ => {
            return Err(ManifestError::new(
                command_key,
                "expected a nonempty array of strings: the executable, then its arguments",
            ));
        }
    };
    let given = match required_string(entry, prefix, "given")?.as_str() {
        "start" => Given::Start,
        "inputs" => Given::Inputs,
        other => {
            return Err(ManifestError::new(
                join(prefix, "given"),
                format!(
                    "`{other}` is no given: `start` (the definition's start configuration, \
                     besides the inputs) or `inputs` (the program's inputs alone)"
                ),
            ));
        }
    };
    let omits = names(entry, prefix, "omits", "cell names")?;
    let identity = match entry.get("identity") {
        None => None,
        Some(value) => {
            let key = join(prefix, "identity");
            let identity = table(value, &key)?;
            known_keys(identity, &key, &["file"])?;
            Some(IdentitySection {
                file: required_string(identity, &key, "file")?,
            })
        }
    };
    let time_ms = match entry.get("time_ms") {
        None => None,
        Some(Value::Integer(value)) if *value > 0 => Some(u64::try_from(*value).expect("positive")),
        Some(Value::Integer(_)) => {
            return Err(ManifestError::new(
                join(prefix, "time_ms"),
                "must be positive",
            ));
        }
        Some(_) => {
            return Err(ManifestError::new(
                join(prefix, "time_ms"),
                "expected an integer",
            ));
        }
    };
    let views_key = join(prefix, "views");
    let entries = match entry.get("views") {
        None => return Err(missing(&views_key)),
        Some(Value::Array(entries)) if !entries.is_empty() => entries,
        Some(Value::Array(_)) => {
            return Err(ManifestError::new(
                views_key,
                "names no view: an implementation is compared under the views it declares; \
                 `views = [{ name = \"end\", required = true }]` compares every cell it states",
            ));
        }
        Some(_) => {
            return Err(ManifestError::new(
                views_key,
                "expected an array of tables, each a view",
            ));
        }
    };
    let mut views = Vec::<ViewSection>::new();
    for (index, view) in entries.iter().enumerate() {
        let key = format!("{views_key}[{index}]");
        let view = view_entry(table(view, &key)?, &key)?;
        if let Some(first) = views.iter().position(|other| other.name == view.name) {
            return Err(ManifestError::new(
                join(&key, "name"),
                format!(
                    "`{}` is declared twice ({views_key}[{first}] declares it first)",
                    view.name
                ),
            ));
        }
        views.push(view);
    }
    Ok(ImplementationSection {
        name,
        command,
        given,
        omits,
        identity,
        time_ms,
        views,
    })
}

fn view_entry(entry: &Table, key: &str) -> Result<ViewSection, ManifestError> {
    known_keys(
        entry,
        key,
        &["name", "required", "compare", "views", "observer"],
    )?;
    let name = nonblank(entry, key, "name")?;
    let required = match entry.get("required") {
        None => false,
        Some(Value::Boolean(required)) => *required,
        Some(_) => {
            return Err(ManifestError::new(
                join(key, "required"),
                "expected a boolean",
            ));
        }
    };
    let mut front_end = serde_json::Map::new();
    if entry.contains_key("compare") {
        let cells = names(entry, key, "compare", "cell names")?;
        if cells.is_empty() {
            return Err(ManifestError::new(
                join(key, "compare"),
                "names no cell: leave `compare` out to compare every cell the implementation \
                 states",
            ));
        }
        front_end.insert("compare".into(), serde_json::json!(cells));
    }
    for name in VIEW_FRONT_END_KEYS.into_iter().skip(1) {
        if let Some(value) = front_end_key(entry, key, name)? {
            front_end.insert(name.into(), value);
        }
    }
    Ok(ViewSection {
        name,
        required,
        front_end,
    })
}

/// A required string that is not blank.
fn nonblank(entry: &Table, prefix: &str, name: &str) -> Result<String, ManifestError> {
    let value = required_string(entry, prefix, name)?;
    if value.trim().is_empty() {
        return Err(ManifestError::new(join(prefix, name), "is blank"));
    }
    Ok(value)
}
