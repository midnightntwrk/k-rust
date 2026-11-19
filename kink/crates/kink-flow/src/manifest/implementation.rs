//! `[[implementation]]`: another implementation of the corpus's system, which `compare` runs on
//! every program and compares with the definition under each of its views ([`crate::compare`]).
//!
//! kink-flow reads the declaration's shape and its own keys (`name`, `protocol`, `command`,
//! `given`, `omits`, `identity`, `time_ms`, each view's `name`, `required` and `channels`); a
//! view's `compare`, `views` and `observer` are the front end's, which only a front end that
//! reads the definition's values resolves (`crate::compare::Vocabulary::check`). An
//! implementation is no input of the definition's runs, so the declaration is in no digest or
//! cache key of them.
//!
//! A view is an *end view*, which compares the implementation's end with the definition's, a
//! *trace view* (`channels`), which compares the elements the implementation states for
//! channels of the flow's `[observe]` with the definition's, or an *acceptance view*
//! (`kind = "accepts"`), which compares whether each side accepts the program. Only an
//! implementation of [`Protocol::V2`] or [`Protocol::V3`] is asked for a trace, and only one of
//! [`Protocol::V3`] can answer that it rejects a program.
//!
//! A view written inline is an anonymous projection. A view may instead name one of the flow's
//! projections, `{ projection = NAME, required = BOOL }` ([`super::ProjectionSection`]): its
//! name is the projection's, and decoding resolves it to a view with the projection's keys
//! ([`ViewSection::projection`]). A projection that compares both an end and channels is no view
//! (a view is an end, a trace or an acceptance view). A projection without `compare` compares
//! every observable cell, where an inline view without `compare` compares every cell the
//! implementation states; the front end that resolves views tells them apart by
//! [`ViewSection::projection`].
//!
//! What makes a declaration no declaration of any flow (a key of the wrong shape, a view with
//! both a trace view's key and an end view's) fails decoding, as every key of the manifest does.
//! What depends on the rest of the flow, or leaves the flow's other commands their meaning (a
//! protocol this build does not speak, a trace view the protocol or `[observe]` does not
//! support), is [`ImplementationSection::declaration`]'s, which only `compare` asks: an
//! implementation is no input of `check`, `run` or `coverage`.

use super::{
    ManifestError, ObserveSection, ProjectionKind, ProjectionSection, front_end_key, join,
    known_keys, missing, names, optional_string, required_string, table,
};
use std::collections::BTreeMap;
use toml::{Table, Value};

/// One `[[implementation]]`, as written.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImplementationSection {
    /// `name`: unique among the manifest's implementations.
    pub name: String,
    /// `protocol`: the protocol its requests and answers are of, as written;
    /// [`Protocol::V1`]'s name where the key is absent. A name of no protocol decodes, and is
    /// [`Self::declaration`]'s refusal; [`Self::protocol`] reads it.
    pub protocol: String,
    /// `command`: the argv that runs the implementation on one program, its first word an
    /// executable: a path with a `/` relative to the manifest's directory, else a name the
    /// system looks up on `PATH`.
    pub command: Vec<String>,
    /// `given`: what each request gives the implementation besides the program's inputs.
    pub given: Given,
    /// `omits`: the cells the implementation does not state, by the front end's cell names;
    /// every other cell a view compares must be in its answer.
    pub omits: Vec<String>,
    /// `identity = { file = .. }`: the file whose digest names the implementation's build, under
    /// which its answers are cached (`crate::compare`); `None`: it runs on every command.
    pub identity: Option<IdentitySection>,
    /// `time_ms`: the wall clock that cancels one run of the implementation; `None`: the
    /// manifest's `budget.time_ms`. It decides no verdict.
    pub time_ms: Option<u64>,
    /// `views`: the views it is compared under, in the order written; at least one.
    pub views: Vec<ViewSection>,
}

/// A protocol an implementation is run by: the shape of its requests and answers.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Protocol {
    /// `kink-implementation/1`: a request of the program's inputs (and start), an answer of the
    /// implementation's end.
    V1,
    /// `kink-implementation/2`: `/1`, where a request may also ask for the elements of
    /// observation channels and an answer state them.
    V2,
    /// `kink-implementation/3`: `/2`, where an answer may also say that the implementation
    /// rejects the program (`end: "rejected"`, with its `message` and the definition's refused
    /// end it names, `refused`).
    V3,
}

impl Protocol {
    /// Every protocol, in order.
    pub const ALL: [Self; 3] = [Self::V1, Self::V2, Self::V3];

    /// The protocol's name, as `protocol` and a request spell it.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::V1 => "kink-implementation/1",
            Self::V2 => "kink-implementation/2",
            Self::V3 => "kink-implementation/3",
        }
    }

    /// The protocol named `name`, if one is.
    #[must_use]
    pub fn parse(name: &str) -> Option<Self> {
        Self::ALL
            .into_iter()
            .find(|protocol| protocol.as_str() == name)
    }

    /// Whether a request of the protocol can ask for a trace, so an implementation of it may
    /// declare a trace view.
    #[must_use]
    pub const fn has_traces(self) -> bool {
        matches!(self, Self::V2 | Self::V3)
    }

    /// Whether an answer of the protocol can say that the implementation rejects the program.
    #[must_use]
    pub const fn has_rejections(self) -> bool {
        matches!(self, Self::V3)
    }
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
    /// `channels`: the channels of the flow's `[observe]` a trace view compares, as written
    /// (without repeats); `None` for an end view. An empty array decodes, and is
    /// [`ImplementationSection::declaration`]'s refusal.
    pub channels: Option<Vec<String>>,
    /// `kind = "accepts"`: an acceptance view, which compares whether each side accepts the
    /// program (`crate::compare`), and has no other key but `name` and `required`.
    pub accepts: bool,
    /// The front end's keys of an end view, as JSON (`compare`, an array of cell names; `views`,
    /// a function by cell; `observer`): which cells are compared, and through which functions of
    /// their values. Empty: every cell the implementation states, as values (for a view naming a
    /// projection: every observable cell); and empty for a trace view, which has none of them.
    pub front_end: serde_json::Map<String, serde_json::Value>,
    /// `projection`: the flow's projection the view names, whose name is the view's and whose
    /// keys decoding copied into the view; `None` for a view written inline.
    pub projection: Option<String>,
}

impl ImplementationSection {
    /// The declaration as documents name it: `{name, command, given, omits, identity, time_ms,
    /// views: [{name, required, ..front end keys}]}`, with `protocol` where it is not
    /// [`Protocol::V1`] and a trace view's `channels`.
    ///
    /// The value is a function of what is declared, so the absent `protocol` and the written
    /// `kink-implementation/1` have one value, the one a declaration had before the key existed:
    /// a record made then still names its declaration. Any other protocol, and every trace
    /// view's channels, are in the value, so a changed declaration has another.
    #[must_use]
    pub fn value(&self) -> serde_json::Value {
        let mut value = self.value_without_protocol();
        if self.protocol != Protocol::V1.as_str() {
            value["protocol"] = serde_json::json!(self.protocol);
        }
        value
    }

    fn value_without_protocol(&self) -> serde_json::Value {
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

    /// The protocol `protocol` names; `None` for a name of no protocol.
    #[must_use]
    pub fn protocol(&self) -> Option<Protocol> {
        Protocol::parse(&self.protocol)
    }

    /// The trace views, in the order written.
    pub fn trace_views(&self) -> impl Iterator<Item = &ViewSection> {
        self.views.iter().filter(|view| view.is_trace())
    }

    /// Whether some view compares the implementation's end's cells (an end view), so that an
    /// answer that ends states them.
    #[must_use]
    pub fn has_end_view(&self) -> bool {
        self.views.iter().any(ViewSection::is_end)
    }

    /// Whether some view is an acceptance view.
    #[must_use]
    pub fn has_accepts_view(&self) -> bool {
        self.views.iter().any(|view| view.accepts)
    }

    /// Check what of the declaration depends on the flow it is written in, `observe` being the
    /// flow's `[observe]` (module documentation). `compare` refuses the command on an `Err`,
    /// stage `implementation`, reason `declaration`, its detail naming the key.
    ///
    /// # Errors
    ///
    /// Why the declaration is none of this flow: a `protocol` that names no protocol; a trace
    /// view under a protocol with no traces, in a flow with no `[observe]`, with no channel, or
    /// naming a channel `[observe]` does not declare.
    pub fn declaration(&self, observe: Option<&ObserveSection>) -> Result<(), String> {
        let Some(protocol) = self.protocol() else {
            return Err(format!(
                "protocol: `{}` is no protocol: {}",
                self.protocol,
                Protocol::ALL
                    .iter()
                    .map(|protocol| format!("`{}`", protocol.as_str()))
                    .collect::<Vec<_>>()
                    .join(" or ")
            ));
        };
        for (index, view) in self.views.iter().enumerate() {
            let Some(channels) = &view.channels else {
                continue;
            };
            let key = format!("views[{index}].channels");
            if !protocol.has_traces() {
                return Err(format!(
                    "{key}: the view `{}` compares a trace, which a request of `{}` cannot ask \
                     for: declare `protocol = \"{}\"`",
                    view.name,
                    protocol.as_str(),
                    Protocol::V2.as_str()
                ));
            }
            let Some(observe) = observe else {
                return Err(format!(
                    "{key}: the view `{}` compares channels of [observe], and the flow declares \
                     none: declare [[observe.point]] or [[observe.log]]",
                    view.name
                ));
            };
            if channels.is_empty() {
                return Err(format!(
                    "{key}: names no channel: a trace view compares the channels of [observe] \
                     it names"
                ));
            }
            let declared = observe.channel_names().collect::<Vec<_>>();
            if let Some((position, channel)) = channels
                .iter()
                .enumerate()
                .find(|(_, channel)| !declared.contains(&channel.as_str()))
            {
                return Err(format!(
                    "{key}[{position}]: `{channel}` is no channel of [observe] (its channels: {})",
                    declared
                        .iter()
                        .map(|name| format!("`{name}`"))
                        .collect::<Vec<_>>()
                        .join(", ")
                ));
            }
        }
        Ok(())
    }

    /// Whether some view of the implementation is required.
    #[must_use]
    pub fn has_required_view(&self) -> bool {
        self.views.iter().any(|view| view.required)
    }
}

impl ViewSection {
    /// Whether the view is a trace view: it names `channels`.
    #[must_use]
    pub const fn is_trace(&self) -> bool {
        self.channels.is_some()
    }

    /// Whether the view is an end view: neither a trace view nor an acceptance view.
    #[must_use]
    pub const fn is_end(&self) -> bool {
        self.channels.is_none() && !self.accepts
    }

    /// The view as documents name it: its name, `required`, and an end view's front-end keys or
    /// a trace view's `channels`, with `projection` for a view naming one (a view written inline
    /// has the value it had before projections existed).
    #[must_use]
    pub fn value(&self) -> serde_json::Value {
        let mut value = self.front_end.clone();
        if let Some(channels) = &self.channels {
            value.insert("channels".into(), serde_json::json!(channels));
        }
        if self.accepts {
            value.insert("kind".into(), serde_json::json!("accepts"));
        }
        if let Some(projection) = &self.projection {
            value.insert("projection".into(), serde_json::json!(projection));
        }
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
            "name", "protocol", "command", "given", "omits", "identity", "time_ms", "views",
        ],
    )?;
    let name = nonblank(entry, prefix, "name")?;
    let protocol = optional_string(entry, prefix, "protocol")?
        .unwrap_or_else(|| Protocol::V1.as_str().to_owned());
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
        protocol,
        command,
        given,
        omits,
        identity,
        time_ms,
        views,
    })
}

fn view_entry(entry: &Table, key: &str) -> Result<ViewSection, ManifestError> {
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
    if entry.contains_key("projection") {
        if let Some(other) = entry
            .keys()
            .find(|other| !["projection", "required"].contains(&other.as_str()))
        {
            return Err(ManifestError::new(
                join(key, other),
                "a view naming a projection (`projection = NAME`) has `projection` and \
                 `required` only: its name and what it compares are the projection's",
            ));
        }
        let projection = nonblank(entry, key, "projection")?;
        // Resolved against the flow's projections once they are decoded ([`resolve_views`]).
        return Ok(ViewSection {
            name: projection.clone(),
            required,
            channels: None,
            accepts: false,
            front_end: serde_json::Map::new(),
            projection: Some(projection),
        });
    }
    known_keys(
        entry,
        key,
        &[
            "name", "required", "kind", "channels", "compare", "views", "observer",
        ],
    )?;
    let name = nonblank(entry, key, "name")?;
    let accepts = match entry.get("kind") {
        None => false,
        Some(Value::String(kind)) if kind == "accepts" => true,
        Some(_) => {
            return Err(ManifestError::new(
                join(key, "kind"),
                "expected \"accepts\" (an acceptance view); an end view and a trace view have no \
                 `kind`",
            ));
        }
    };
    if accepts
        && let Some(other) = ["channels"]
            .into_iter()
            .chain(VIEW_FRONT_END_KEYS)
            .find(|other| entry.contains_key(*other))
    {
        return Err(ManifestError::new(
            join(key, other),
            "an acceptance view (`kind = \"accepts\"`) compares whether each side accepts the \
             program, and has `name` and `required` only",
        ));
    }
    let channels = if entry.contains_key("channels") {
        // The two kinds of view share no key but `name` and `required`: `compare`, `views` and
        // `observer` say how two ends are compared, and a trace view compares no end.
        if let Some(other) = VIEW_FRONT_END_KEYS
            .into_iter()
            .find(|other| entry.contains_key(*other))
        {
            return Err(ManifestError::new(
                join(key, "channels"),
                format!(
                    "a view with `channels` is a trace view, which compares the channels' \
                     elements; `{other}` is an end view's, which compares cells of the end: \
                     declare two views"
                ),
            ));
        }
        Some(names(entry, key, "channels", "channel names")?)
    } else {
        None
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
        channels,
        accepts,
        front_end,
        projection: None,
    })
}

/// Each view of `implementations` that names a projection, given the keys of the projection of
/// that name among `projections` (the flow's, the implicit `default` included).
///
/// # Errors
///
/// A view naming no projection of the flow, or one that compares an end and channels.
pub(super) fn resolve_views(
    implementations: &mut [ImplementationSection],
    projections: &[ProjectionSection],
) -> Result<(), ManifestError> {
    // The implementation that first names each snapshot projection: its snapshots
    // (`snapshots/<projection>/<case id>`) name no implementation, so one produces them.
    let mut snapshot_producers = BTreeMap::<String, usize>::new();
    for (index, implementation) in implementations.iter_mut().enumerate() {
        for (position, view) in implementation.views.iter_mut().enumerate() {
            let Some(name) = view.projection.clone() else {
                continue;
            };
            let key = format!("implementation[{index}].views[{position}].projection");
            let Some(projection) = projections
                .iter()
                .find(|projection| projection.name == name)
            else {
                return Err(ManifestError::new(
                    key,
                    format!(
                        "`{name}` is no projection of the flow (its projections: {})",
                        projections
                            .iter()
                            .map(|projection| format!("`{}`", projection.name))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                ));
            };
            if projection.is_snapshot()
                && let Some(first) = snapshot_producers.get(&name).copied()
                && first != index
            {
                return Err(ManifestError::new(
                    key,
                    format!(
                        "the projection `{name}` is a snapshot, and implementation[{first}] \
                         names it first: its snapshots (`snapshots/{name}/<case id>`) hold one \
                         implementation's values, so each snapshot projection is named by one \
                         implementation"
                    ),
                ));
            }
            if projection.is_snapshot() {
                snapshot_producers.insert(name.clone(), index);
            }
            match projection.kind {
                ProjectionKind::Accepts => view.accepts = true,
                ProjectionKind::Trace => view.channels.clone_from(&projection.channels),
                ProjectionKind::End => {
                    if projection.channels.is_some() {
                        return Err(ManifestError::new(
                            key,
                            format!(
                                "the projection `{name}` compares the end's cells and channels, \
                                 and a view compares one of them: name an `end` projection \
                                 without `channels`, a `trace` projection or an `accepts` \
                                 projection"
                            ),
                        ));
                    }
                    view.front_end.clone_from(&projection.front_end);
                    if let Some(compare) = &projection.compare {
                        view.front_end
                            .insert("compare".into(), serde_json::json!(compare));
                    }
                }
            }
        }
    }
    Ok(())
}

/// A required string that is not blank.
fn nonblank(entry: &Table, prefix: &str, name: &str) -> Result<String, ManifestError> {
    let value = required_string(entry, prefix, name)?;
    if value.trim().is_empty() {
        return Err(ManifestError::new(join(prefix, name), "is blank"));
    }
    Ok(value)
}

#[cfg(test)]
mod tests {
    use super::{ImplementationSection, Protocol};
    use crate::admit::InputFiles;
    use crate::compare::{
        CompareOptions, Judged, Question, TraceAnswer, TraceQuestion, Vocabulary, command,
    };
    use crate::manifest::{FlowManifest, Program};
    use k_rust::kore::ast::Pattern;
    use serde_json::{Value, json};
    use std::path::Path;

    const HEAD: &str = "[spec]\nentry = \"calc.k\"\nmain_module = \"CALC\"\n\n";

    const OBSERVE: &str = "[[observe.point]]\nname = \"ticks\"\nbefore = [\"CALC.tick\"]\nstutter \
                           = \"count\"\ncells = [\"n\"]\n\n[[observe.log]]\nname = \
                           \"writes\"\ncell = \"bus\"\nat = [\"ticks\"]\n\n";

    /// A declaration as one was written before `protocol` and `channels` existed, with every
    /// key it could have.
    const V1: &str = "name = \"cpu\"\ncommand = [\"bin/cpu\", \"--kink\"]\ngiven = \
                      \"start\"\nomits = [\"k\"]\nidentity = { file = \"bin/cpu\" }\ntime_ms = \
                      5\nviews = [{ name = \"writes\", views = { bus = \"WritesView\" }, observer \
                      = \"p:views\", required = true }, { name = \"all\", compare = [\"pc\"] }]\n";

    /// The bytes of [`V1`]'s value as the build before `protocol` and `channels` wrote them
    /// (taken from that build): every document and lock that names the declaration holds them.
    const V1_VALUE: &str = r#"{"command":["bin/cpu","--kink"],"given":"start","identity":{"file":"bin/cpu"},"name":"cpu","omits":["k"],"time_ms":5,"views":[{"name":"writes","observer":"p:views","required":true,"views":{"bus":"WritesView"}},{"compare":["pc"],"name":"all","required":false}]}"#;

    fn decoded(text: &str) -> Result<FlowManifest, crate::ManifestError> {
        FlowManifest::decode(&format!("{HEAD}{text}"), Path::new("."))
    }

    fn one(text: &str) -> ImplementationSection {
        decoded(text).unwrap().implementations.remove(0)
    }

    /// An implementation `x` with `keys` before its `views`.
    fn x(keys: &str, views: &str) -> String {
        format!(
            "[[implementation]]\nname = \"x\"\n{keys}command = [\"x\"]\ngiven = \
             \"inputs\"\nviews = [{views}]\n"
        )
    }

    const V2: &str = "protocol = \"kink-implementation/2\"\n";

    #[test]
    fn a_protocol_1_declaration_has_the_value_it_had() {
        let absent = one(&format!("[[implementation]]\n{V1}"));
        assert_eq!(absent.protocol(), Some(Protocol::V1));
        assert_eq!(serde_json::to_string(&absent.value()).unwrap(), V1_VALUE);
        // The written default is the same declaration, so it has the same value.
        let written = one(&format!(
            "[[implementation]]\nprotocol = \"kink-implementation/1\"\n{V1}"
        ));
        assert_eq!(written.protocol(), Some(Protocol::V1));
        assert_eq!(serde_json::to_string(&written.value()).unwrap(), V1_VALUE);
        assert!(absent.views.iter().all(|view| !view.is_trace()));
        assert_eq!(absent.declaration(None), Ok(()));
    }

    #[test]
    fn a_protocol_and_a_trace_view_are_in_the_declared_value() {
        let end = "{ name = \"end\", required = true }";
        let trace = "{ name = \"t\", channels = [\"writes\", \"ticks\"], required = true }";
        let v1 = one(&x("", end));
        let v2 = one(&x(V2, end));
        assert_eq!(v2.protocol(), Some(Protocol::V2));
        let mut expected = v1.value();
        assert!(expected.get("protocol").is_none());
        expected["protocol"] = json!("kink-implementation/2");
        assert_eq!(v2.value(), expected);
        let traced = one(&format!("{OBSERVE}{}", x(V2, &format!("{end}, {trace}"))));
        assert_eq!(
            traced.declaration(decoded(OBSERVE).unwrap().observe.as_ref()),
            Ok(())
        );
        assert_eq!(
            traced.views[1].channels.as_deref(),
            Some(&["writes".to_owned(), "ticks".to_owned()][..])
        );
        assert!(traced.views[1].is_trace() && !traced.views[0].is_trace());
        assert_eq!(traced.trace_views().count(), 1);
        assert_eq!(
            traced.views[1].value(),
            json!({"name": "t", "required": true, "channels": ["writes", "ticks"]})
        );
        // A changed list of channels is another declaration.
        let other = one(&format!(
            "{OBSERVE}{}",
            x(
                V2,
                "{ name = \"t\", channels = [\"ticks\"], required = true }"
            )
        ));
        assert_ne!(other.views[0].value(), traced.views[1].value());
    }

    #[test]
    fn a_view_of_the_wrong_shape_does_not_decode() {
        for (views, expected) in [
            (
                "{ name = \"t\", channels = [\"ticks\"], compare = [\"pc\"] }",
                "implementation[0].views[0].channels: a view with `channels` is a trace view, \
                 which compares the channels' elements; `compare` is an end view's",
            ),
            (
                "{ name = \"t\", channels = [\"ticks\"], views = { bus = \"W\" } }",
                "implementation[0].views[0].channels: a view with `channels` is a trace view, \
                 which compares the channels' elements; `views` is an end view's",
            ),
            (
                "{ name = \"t\", channels = [\"ticks\"], observer = \"p:d\" }",
                "implementation[0].views[0].channels: a view with `channels` is a trace view, \
                 which compares the channels' elements; `observer` is an end view's",
            ),
            (
                "{ name = \"t\", channels = \"ticks\" }",
                "implementation[0].views[0].channels: expected an array of channel names",
            ),
            (
                "{ name = \"t\", channels = [1] }",
                "implementation[0].views[0].channels[0]: expected a nonempty string",
            ),
            (
                "{ name = \"t\", channels = [\"ticks\", \"ticks\"] }",
                "implementation[0].views[0].channels: names `ticks` twice",
            ),
        ] {
            let error = decoded(&format!("{OBSERVE}{}", x(V2, views)))
                .unwrap_err()
                .to_string();
            assert!(error.starts_with(expected), "{views}\n{error}");
        }
        let error = decoded(&x("protocol = 2\n", "{ name = \"end\" }"))
            .unwrap_err()
            .to_string();
        assert!(error.starts_with("implementation[0].protocol: "), "{error}");
    }

    /// A front end that accepts every declaration and is asked nothing else: a refusal of the
    /// declaration comes before any run.
    struct Accepts;

    impl Vocabulary for Accepts {
        fn check(&self, _: &ImplementationSection) -> Result<(), String> {
            Ok(())
        }
        fn start(&self, _: &Pattern) -> Result<Value, String> {
            unreachable!("no run")
        }
        fn inputs(&self, _: &Program, _: &mut dyn InputFiles) -> Result<Value, String> {
            unreachable!("no run")
        }
        fn read_answer(&self, _: &ImplementationSection, _: &Value) -> Result<(), String> {
            unreachable!("no run")
        }
        fn compare(&self, _: &Question<'_>) -> Result<Judged, String> {
            unreachable!("no run")
        }
        fn observe_request(&self, _: &[String]) -> Result<Vec<Value>, String> {
            unreachable!("no run")
        }
        fn judge_trace(&self, _: &TraceQuestion<'_>) -> Result<TraceAnswer, String> {
            unreachable!("no run")
        }
    }

    #[test]
    fn compare_refuses_a_declaration_that_is_none_of_the_flow() {
        let trace = "{ name = \"t\", channels = [\"ticks\"] }";
        for (text, expected) in [
            (
                format!("{OBSERVE}{}", x("", trace)),
                "implementation `x`: views[0].channels: the view `t` compares a trace, which a \
                 request of `kink-implementation/1` cannot ask for: declare `protocol = \
                 \"kink-implementation/2\"`",
            ),
            (
                x(V2, trace),
                "implementation `x`: views[0].channels: the view `t` compares channels of \
                 [observe], and the flow declares none",
            ),
            (
                format!(
                    "{OBSERVE}{}",
                    x(
                        V2,
                        "{ name = \"end\" }, { name = \"t\", channels = [\"ticks\", \"tocks\"] }"
                    )
                ),
                "implementation `x`: views[1].channels[1]: `tocks` is no channel of [observe] \
                 (its channels: `ticks`, `writes`)",
            ),
            (
                format!("{OBSERVE}{}", x(V2, "{ name = \"t\", channels = [] }")),
                "implementation `x`: views[0].channels: names no channel",
            ),
            (
                x(
                    "protocol = \"kink-implementation/4\"\n",
                    "{ name = \"end\" }",
                ),
                "implementation `x`: protocol: `kink-implementation/4` is no protocol: \
                 `kink-implementation/1` or `kink-implementation/2` or `kink-implementation/3`",
            ),
        ] {
            let manifest = decoded(&text).unwrap();
            let document = command(
                &manifest,
                &CompareOptions::default(),
                Some(&Accepts),
                "kink-flow compare",
            );
            let refusal = &document["refusal"];
            assert_eq!(refusal["stage"], "implementation", "{text}\n{document}");
            assert_eq!(refusal["reason"], "declaration", "{text}\n{document}");
            let detail = refusal["detail"].as_str().unwrap();
            assert!(detail.starts_with(expected), "{text}\n{detail}");
            assert!(document["rows"].as_array().unwrap().is_empty());
        }
    }

    /// A view may name a projection of the flow, `{ projection = NAME, required = BOOL }`
    /// (projections package, PJ-10): its name is the projection's, and decoding gives it the
    /// projection's keys, so compare reads it as it reads a view written inline.
    #[test]
    fn a_view_naming_a_projection_is_resolved_to_its_keys() {
        let projections = "[[projection]]\nname = \"regs\"\ncompare = [\"regs\"]\nviews = { regs \
                           = \"RegsView\" }\nobserver = \"p:views\"\n\n[[projection]]\nname = \
                           \"a\"\nkind = \"accepts\"\n\n[[projection]]\nname = \"t\"\nkind = \
                           \"trace\"\nchannels = [\"ticks\"]\n\n[[projection]]\nname = \
                           \"all\"\n\n";
        let manifest = decoded(&format!(
            "{OBSERVE}{projections}{}",
            x(
                V2,
                "{ projection = \"regs\", required = true }, { projection = \"a\" }, \
                 { projection = \"t\", required = true }, { projection = \"all\" }, \
                 { name = \"end\" }"
            )
        ))
        .unwrap();
        let views = &manifest.implementations[0].views;
        let names = views
            .iter()
            .map(|view| view.name.as_str())
            .collect::<Vec<_>>();
        assert_eq!(names, ["regs", "a", "t", "all", "end"]);
        assert!(views[0].is_end() && views[0].required);
        assert_eq!(
            views[0].value(),
            json!({
                "name": "regs", "required": true, "projection": "regs", "compare": ["regs"],
                "views": {"regs": "RegsView"}, "observer": "p:views",
            })
        );
        assert!(views[1].accepts && !views[1].required);
        assert_eq!(
            views[1].value(),
            json!({"name": "a", "required": false, "projection": "a", "kind": "accepts"})
        );
        assert!(views[2].is_trace());
        assert_eq!(views[2].channels, Some(vec!["ticks".to_owned()]));
        // A projection without `compare` compares every observable cell; the view says which
        // projection it is, unlike a view written inline, which compares every cell stated.
        assert!(views[3].is_end() && views[3].front_end.is_empty());
        assert_eq!(views[3].projection.as_deref(), Some("all"));
        assert_eq!(views[4].projection, None);
        assert_eq!(views[4].value(), json!({"name": "end", "required": false}));
        assert_eq!(
            manifest.implementations[0].declaration(manifest.observe.as_ref()),
            Ok(())
        );
        // The implicit `default` of a flow without projections and without `[observe]` is an
        // end view of every observable cell.
        let default = one(&x("", "{ projection = \"default\", required = true }"));
        assert!(default.views[0].is_end() && default.views[0].front_end.is_empty());
        assert_eq!(default.views[0].name, "default");
    }

    #[test]
    fn a_view_naming_no_projection_of_one_view_kind_does_not_decode() {
        let end_and_channels =
            "[[projection]]\nname = \"both\"\ncompare = [\"pc\"]\nchannels = [\"ticks\"]\n\n";
        for (text, expected) in [
            (
                x("", "{ projection = \"nope\" }"),
                "implementation[0].views[0].projection: `nope` is no projection of the flow (its \
                 projections: `default`)",
            ),
            (
                x("", "{ projection = \"default\", name = \"d\" }"),
                "implementation[0].views[0].name: a view naming a projection",
            ),
            (
                x("", "{ projection = \"default\", compare = [\"pc\"] }"),
                "implementation[0].views[0].compare: a view naming a projection",
            ),
            (
                x("", "{ projection = \"default\" }, { name = \"default\" }"),
                "implementation[0].views[1].name: `default` is declared twice",
            ),
            (
                format!(
                    "{OBSERVE}{end_and_channels}{}",
                    x(V2, "{ projection = \"both\" }")
                ),
                "implementation[0].views[0].projection: the projection `both` compares the end's \
                 cells and channels",
            ),
            // With `[observe]`, the implicit default compares the end and every channel.
            (
                format!("{OBSERVE}{}", x(V2, "{ projection = \"default\" }")),
                "implementation[0].views[0].projection: the projection `default` compares the \
                 end's cells and channels",
            ),
        ] {
            let error = decoded(&text).unwrap_err().to_string();
            assert!(error.starts_with(expected), "{text}\n{error}");
        }
    }

    /// An acceptance view (`kind = "accepts"`) has `name` and `required` only, and is refused
    /// before any run over a definition that declares no `finished` end (projections PJ-02).
    #[test]
    fn an_acceptance_view_is_declared_and_refused_without_a_finished_end() {
        let manifest = decoded(&x(
            "",
            "{ name = \"a\", kind = \"accepts\", required = true }",
        ))
        .unwrap();
        let view = &manifest.implementations[0].views[0];
        assert!(view.accepts && !view.is_end() && !view.is_trace());
        assert_eq!(
            view.value(),
            json!({"name": "a", "required": true, "kind": "accepts"})
        );
        for (views, expected) in [
            (
                "{ name = \"a\", kind = \"accepts\", compare = [\"n\"] }",
                "implementation[0].views[0].compare: an acceptance view",
            ),
            (
                "{ name = \"a\", kind = \"accepts\", channels = [\"ticks\"] }",
                "implementation[0].views[0].channels: an acceptance view",
            ),
            (
                "{ name = \"a\", kind = \"end\" }",
                "implementation[0].views[0].kind: expected \"accepts\"",
            ),
        ] {
            let error = decoded(&x("", views)).unwrap_err().to_string();
            assert!(error.starts_with(expected), "{views}\n{error}");
        }
        let document = command(
            &manifest,
            &CompareOptions::default(),
            Some(&Accepts),
            "kink-flow compare",
        );
        assert_eq!(document["refusal"]["stage"], "implementation", "{document}");
        assert_eq!(
            document["refusal"]["reason"], "no-finished-end",
            "{document}"
        );
        assert!(document["rows"].as_array().unwrap().is_empty());
    }
}
