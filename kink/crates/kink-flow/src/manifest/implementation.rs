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
//! A view is an *end view*, which compares the implementation's end with the definition's, or a
//! *trace view* (`channels`), which compares the elements the implementation states for
//! channels of the flow's `[observe]` with the definition's. Only an implementation of
//! [`Protocol::V2`] is asked for a trace.
//!
//! What makes a declaration no declaration of any flow (a key of the wrong shape, a view with
//! both a trace view's key and an end view's) fails decoding, as every key of the manifest does.
//! What depends on the rest of the flow, or leaves the flow's other commands their meaning (a
//! protocol this build does not speak, a trace view the protocol or `[observe]` does not
//! support), is [`ImplementationSection::declaration`]'s, which only `compare` asks: an
//! implementation is no input of `check`, `run` or `coverage`.

use super::{
    ManifestError, ObserveSection, front_end_key, join, known_keys, missing, names,
    optional_string, required_string, table,
};
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
}

impl Protocol {
    /// Every protocol, in order.
    pub const ALL: [Self; 2] = [Self::V1, Self::V2];

    /// The protocol's name, as `protocol` and a request spell it.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::V1 => "kink-implementation/1",
            Self::V2 => "kink-implementation/2",
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
        matches!(self, Self::V2)
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
    /// The front end's keys of an end view, as JSON (`compare`, an array of cell names; `views`,
    /// a function by cell; `observer`): which cells are compared, and through which functions of
    /// their values. Empty: every cell the implementation states, as values; and empty for a
    /// trace view, which has none of them.
    pub front_end: serde_json::Map<String, serde_json::Value>,
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

    /// The view as documents name it: its name, `required`, and an end view's front-end keys or
    /// a trace view's `channels`.
    #[must_use]
    pub fn value(&self) -> serde_json::Value {
        let mut value = self.front_end.clone();
        if let Some(channels) = &self.channels {
            value.insert("channels".into(), serde_json::json!(channels));
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
    known_keys(
        entry,
        key,
        &[
            "name", "required", "channels", "compare", "views", "observer",
        ],
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

#[cfg(test)]
mod tests {
    use super::{ImplementationSection, Protocol};
    use crate::admit::InputFiles;
    use crate::compare::{CompareOptions, Judged, Question, Vocabulary, command};
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
                    "protocol = \"kink-implementation/3\"\n",
                    "{ name = \"end\" }",
                ),
                "implementation `x`: protocol: `kink-implementation/3` is no protocol: \
                 `kink-implementation/1` or `kink-implementation/2`",
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
}
