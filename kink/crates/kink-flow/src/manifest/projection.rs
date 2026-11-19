//! `[[projection]]`: a named function under which the flow's corpus is measured (projections
//! package, README "The model"): what of each side's raw result is observed (`kind`, `compare`,
//! `views`, `observer`, `channels`) and on which cases (`domain`).
//!
//! A flow that declares no projection has one, `default`: every observable cell of the end and
//! every channel of `[observe]` ([`default_projection`]), which is what a kill compared before
//! projections existed. A flow that declares projections has exactly those.
//!
//! The result record keeps the cells the declared projections compare ([`record_cells`]), so that
//! every command reads the definition's side of each projection from one record: an `end`
//! projection keeps the cells its `compare` names (every observable cell without `compare`); an
//! `accepts` projection keeps every observable cell, since acceptance is the class of the
//! definition's declared ends, which the front end reads from the end's cells by functions
//! kink-flow cannot name; a `trace` projection keeps no cell, since channels are recorded during
//! the run, independent of the end. An implementation's views are not projections of the flow and
//! keep nothing: an `[[implementation]]` is no input of the definition's runs.
//!
//! A projection's `domain` is the programs it applies to ([`ProjectionSection::holds`]): those
//! whose id, or whose case document's path, one of its case patterns matches. `compare` measures
//! a view naming the projection on those programs only; `run` does not apply it yet.
//!
//! A projection's `relation` says what its observed values are judged against: absent, each
//! side's against the definition's; `snapshot`, an implementation's against the value a user
//! accepted for the case, a file beside the flow (`crate::snapshot`). A snapshot relation reads no
//! side of the definition.
//!
//! kink-flow reads the declaration's shape and its own keys (`name`, `kind`, `compare`,
//! `channels`, `domain`, `relation`); `views` and `observer` are the front end's, as a view's are
//! ([`super::ViewSection::front_end`]), and kink-flow's own K front end refuses a projection that
//! has them (`crate::admit`, stage `projection`).

use super::{
    ManifestError, ObserveSection, Program, case_pattern::CasePattern, front_end_key, join,
    known_keys, names, required_string, table,
};
use toml::Value;

/// The name of the projection a flow without `[[projection]]` has.
pub const DEFAULT_PROJECTION: &str = "default";

/// One `[[projection]]`, as written, or the implicit [`default_projection`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProjectionSection {
    /// `name`: unique among the flow's projections.
    pub name: String,
    /// `kind`: what of a result the projection observes; [`ProjectionKind::End`] by default.
    pub kind: ProjectionKind,
    /// `compare`: the cells an `end` projection compares, as written (the front end's cell
    /// names), nonempty and without repeats; `None`: every observable cell. Always `None` for
    /// another kind.
    pub compare: Option<Vec<String>>,
    /// The front end's keys of an `end` projection, as JSON (`views`, a function by cell;
    /// `observer`): through which functions of their values the cells are compared. Empty: the
    /// values as they are; and empty for another kind.
    pub front_end: serde_json::Map<String, serde_json::Value>,
    /// `channels`: the channels of the flow's `[observe]` the projection compares, as written,
    /// nonempty and without repeats: a `trace` projection's (required) or an `end` projection's
    /// besides its cells; `None`: no channel.
    pub channels: Option<Vec<String>>,
    /// `domain`: the cases the projection applies to, as case patterns
    /// ([`super::Program`]'s `files` grammar), as written, each matching some program of the
    /// flow; `None`: every case ([`Self::holds`]).
    pub domain: Option<Vec<String>>,
    /// `relation`: what the observed values are judged against; [`Relation::Definition`] by
    /// default.
    pub relation: Relation,
}

/// What a projection's observed values are judged against.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Relation {
    /// No `relation`: each side's observed value against the definition's.
    #[default]
    Definition,
    /// `relation = "snapshot"`: an implementation's observed value against the value a user
    /// accepted for the case (`crate::snapshot`): under an `accepts` projection its whole answer
    /// to whether it accepts the case (`accepted`, `rejected` with its `message` and `refused`,
    /// `crashed`), under an `end` projection the end as the answer states it.
    Snapshot,
}

/// What a projection observes of each side's result.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProjectionKind {
    /// `end`: the end's cells (`compare`), through the functions `views` names, and any
    /// `channels` besides.
    End,
    /// `accepts`: whether the side accepts the case (`crate::compare`, acceptance views).
    Accepts,
    /// `trace`: the elements of `channels` of `[observe]`.
    Trace,
}

impl ProjectionKind {
    /// The kind as `kind` writes it.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::End => "end",
            Self::Accepts => "accepts",
            Self::Trace => "trace",
        }
    }
}

/// One cell the result record keeps, with the first projection whose `compare` names it
/// ([`record_cells`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RecordCell {
    /// The cell, by the name the front end gave it (a K name once the front end bound it).
    pub cell: String,
    /// The projection that names it first, in the order written.
    pub projection: String,
}

impl ProjectionSection {
    /// Whether the projection compares cells through a function of their values (`views`) or in
    /// another definition (`observer`): only a front end that reads values resolves either.
    #[must_use]
    pub fn has_front_end_keys(&self) -> bool {
        !self.front_end.is_empty()
    }

    /// Whether every observable cell must be in the result record for this projection to be
    /// read from it (module documentation).
    #[must_use]
    pub const fn keeps_every_cell(&self) -> bool {
        match self.kind {
            ProjectionKind::End => self.compare.is_none(),
            ProjectionKind::Accepts => true,
            ProjectionKind::Trace => false,
        }
    }

    /// Whether `program` is in the projection's domain: always without `domain`; otherwise
    /// where one of its patterns matches the program's id or, for a case of a case document, the
    /// document's path as matched (`Program::case`), so a pattern written as a `[[program]]`
    /// entry's holds every program that entry gives, a document's named cases
    /// (`<document>#<name>`) included. The id of a `files` match or of a document's one case is
    /// the path the pattern matched, relative to the case root; a listed program's is its `id`.
    #[must_use]
    pub fn holds(&self, program: &Program) -> bool {
        self.domain.as_ref().is_none_or(|patterns| {
            patterns
                .iter()
                .any(|pattern| pattern_holds(pattern, program))
        })
    }

    /// Whether the projection's relation is a snapshot ([`Relation::Snapshot`]).
    #[must_use]
    pub fn is_snapshot(&self) -> bool {
        self.relation == Relation::Snapshot
    }

    /// The projection as documents name it: `{name, kind}` with the keys it has (`compare`,
    /// `views`, `observer`, `channels`, `domain`, `relation`).
    #[must_use]
    pub fn value(&self) -> serde_json::Value {
        let mut value = self.front_end.clone();
        if let Some(compare) = &self.compare {
            value.insert("compare".into(), serde_json::json!(compare));
        }
        if let Some(channels) = &self.channels {
            value.insert("channels".into(), serde_json::json!(channels));
        }
        if let Some(domain) = &self.domain {
            value.insert("domain".into(), serde_json::json!(domain));
        }
        if self.is_snapshot() {
            value.insert("relation".into(), serde_json::json!("snapshot"));
        }
        value.insert("kind".into(), serde_json::json!(self.kind.as_str()));
        value.insert("name".into(), serde_json::json!(self.name));
        serde_json::Value::Object(value)
    }
}

/// The projection of a flow that declares none: every observable cell of the end, and every
/// channel of `observe` (none without it).
#[must_use]
pub fn default_projection(observe: Option<&ObserveSection>) -> ProjectionSection {
    ProjectionSection {
        name: DEFAULT_PROJECTION.to_owned(),
        kind: ProjectionKind::End,
        compare: None,
        front_end: serde_json::Map::new(),
        channels: observe.map(|observe| observe.channel_names().map(str::to_owned).collect()),
        domain: None,
        relation: Relation::Definition,
    }
}

/// The cells the result record keeps for `declared` (module documentation): `None`, every
/// observable cell, when no projection is declared or one keeps every cell; otherwise the union
/// of the `end` projections' `compare`, in the order written, each cell once with the first
/// projection that names it (empty when every projection is a `trace` projection).
#[must_use]
pub fn record_cells(declared: &[ProjectionSection]) -> Option<Vec<RecordCell>> {
    if declared.is_empty() || declared.iter().any(ProjectionSection::keeps_every_cell) {
        return None;
    }
    let mut cells = Vec::<RecordCell>::new();
    for projection in declared {
        for cell in projection.compare.iter().flatten() {
            if !cells.iter().any(|kept| &kept.cell == cell) {
                cells.push(RecordCell {
                    cell: cell.clone(),
                    projection: projection.name.clone(),
                });
            }
        }
    }
    Some(cells)
}

/// Whether the case pattern `pattern` holds `program` ([`ProjectionSection::holds`]); a pattern
/// that does not parse holds nothing (decoding refuses one).
fn pattern_holds(pattern: &str, program: &Program) -> bool {
    CasePattern::parse(pattern, "the corpus root").is_ok_and(|pattern| {
        pattern.matches_path(&program.id)
            || program
                .case
                .as_deref()
                .is_some_and(|document| pattern.matches_path(document))
    })
}

/// The `compare` of each declared `end` projection that has one, each cell with the projection,
/// in the order written: what admission checks of each projection where the result record does
/// not narrow to it (`crate::observed::result_projection`).
#[must_use]
pub fn compare_cells(declared: &[ProjectionSection]) -> Vec<Vec<RecordCell>> {
    declared
        .iter()
        .filter_map(|projection| {
            projection.compare.as_ref().map(|cells| {
                cells
                    .iter()
                    .map(|cell| RecordCell {
                        cell: cell.clone(),
                        projection: projection.name.clone(),
                    })
                    .collect()
            })
        })
        .collect()
}

/// Every pattern of every projection's `domain` holds some program of `programs`, or the
/// manifest is refused at the pattern (`projection[i].domain[j]`): a pattern that matches nothing
/// is an error, as a `[[program]]` pattern's is, since a projection measured on no case measures
/// nothing.
pub(super) fn domains_hold(
    projections: &[ProjectionSection],
    programs: &[Program],
) -> Result<(), ManifestError> {
    for (index, projection) in projections.iter().enumerate() {
        for (at, pattern) in projection.domain.iter().flatten().enumerate() {
            if !programs
                .iter()
                .any(|program| pattern_holds(pattern, program))
            {
                return Err(ManifestError::new(
                    format!("projection[{index}].domain[{at}]"),
                    format!(
                        "pattern {pattern:?} matches no program of the flow (a program's id, or \
                         the path of the case document a case is in); a domain that holds no \
                         case measures nothing"
                    ),
                ));
            }
        }
    }
    Ok(())
}

/// The keys of an `end` projection a front end reads ([`front_end_key`]).
const PROJECTION_FRONT_END_KEYS: [&str; 2] = ["views", "observer"];

/// `[[projection]]`: an array of tables, each name unique, each channel one of `observe`'s.
pub(super) fn projections(
    value: &Value,
    observe: Option<&ObserveSection>,
) -> Result<Vec<ProjectionSection>, ManifestError> {
    let Value::Array(entries) = value else {
        return Err(ManifestError::new(
            "projection",
            "expected [[projection]] tables",
        ));
    };
    let mut projections = Vec::<ProjectionSection>::new();
    for (index, entry) in entries.iter().enumerate() {
        let prefix = format!("projection[{index}]");
        let projection = projection(entry, &prefix, observe)?;
        if let Some(first) = projections
            .iter()
            .position(|other| other.name == projection.name)
        {
            return Err(ManifestError::new(
                join(&prefix, "name"),
                format!(
                    "`{}` is declared twice (projection[{first}] declares it first)",
                    projection.name
                ),
            ));
        }
        projections.push(projection);
    }
    Ok(projections)
}

fn projection(
    value: &Value,
    prefix: &str,
    observe: Option<&ObserveSection>,
) -> Result<ProjectionSection, ManifestError> {
    let entry = table(value, prefix)?;
    known_keys(
        entry,
        prefix,
        &[
            "name", "kind", "compare", "views", "observer", "channels", "domain", "relation",
        ],
    )?;
    let name = required_string(entry, prefix, "name")?;
    if name.trim().is_empty() {
        return Err(ManifestError::new(join(prefix, "name"), "is blank"));
    }
    let kind = match entry.get("kind") {
        None => ProjectionKind::End,
        Some(Value::String(kind)) => match kind.as_str() {
            "end" => ProjectionKind::End,
            "accepts" => ProjectionKind::Accepts,
            "trace" => ProjectionKind::Trace,
            "metric" => {
                return Err(ManifestError::new(
                    join(prefix, "kind"),
                    "`metric` is not a kind of this build: a measurement projection needs \
                     implementations to state metrics, which no protocol does yet",
                ));
            }
            other => return Err(no_kind(prefix, &format!("`{other}` is no kind"))),
        },
        Some(_) => return Err(no_kind(prefix, "expected a string")),
    };
    // The keys each kind observes by: an `end` projection its cells (and channels besides), a
    // `trace` projection its channels, an `accepts` projection nothing but acceptance.
    let allowed: &[&str] = match kind {
        ProjectionKind::End => &["compare", "views", "observer", "channels"],
        ProjectionKind::Accepts => &[],
        ProjectionKind::Trace => &["channels"],
    };
    if let Some(other) = ["compare", "views", "observer", "channels"]
        .into_iter()
        .find(|key| entry.contains_key(*key) && !allowed.contains(key))
    {
        return Err(ManifestError::new(
            join(prefix, other),
            match kind {
                ProjectionKind::Accepts => {
                    "an `accepts` projection compares whether each side accepts the case, and \
                     has no `compare`, `views`, `observer` or `channels`"
                }
                _ => {
                    "a `trace` projection compares the elements of its `channels`; `compare`, \
                     `views` and `observer` are an `end` projection's"
                }
            },
        ));
    }
    let compare = if entry.contains_key("compare") {
        let cells = names(entry, prefix, "compare", "cell names")?;
        if cells.is_empty() {
            return Err(ManifestError::new(
                join(prefix, "compare"),
                "names no cell: leave `compare` out to compare every observable cell",
            ));
        }
        Some(cells)
    } else {
        None
    };
    let mut front_end = serde_json::Map::new();
    for key in PROJECTION_FRONT_END_KEYS {
        if let Some(value) = front_end_key(entry, prefix, key)? {
            front_end.insert(key.into(), value);
        }
    }
    let channels = if entry.contains_key("channels") {
        let channels = names(entry, prefix, "channels", "channel names")?;
        channels_declared(&channels, prefix, observe)?;
        Some(channels)
    } else if kind == ProjectionKind::Trace {
        return Err(ManifestError::new(
            join(prefix, "channels"),
            "missing: a `trace` projection compares the channels of [observe] it names",
        ));
    } else {
        None
    };
    let domain = match entry.get("domain") {
        None => None,
        Some(Value::Array(_)) => {
            let patterns = names(entry, prefix, "domain", "case patterns")?;
            if patterns.is_empty() {
                return Err(ManifestError::new(
                    join(prefix, "domain"),
                    "names no case: leave `domain` out to apply the projection to every case",
                ));
            }
            for (index, pattern) in patterns.iter().enumerate() {
                CasePattern::parse(pattern, "the corpus root").map_err(|reason| {
                    ManifestError::new(format!("{}[{index}]", join(prefix, "domain")), reason)
                })?;
            }
            Some(patterns)
        }
        Some(_) => {
            return Err(ManifestError::new(
                join(prefix, "domain"),
                "expected an array of case patterns",
            ));
        }
    };
    let relation = relation(entry, prefix, kind)?;
    Ok(ProjectionSection {
        name,
        kind,
        compare,
        front_end,
        channels,
        domain,
        relation,
    })
}

/// `relation`: absent, or `"snapshot"` on an `accepts` projection or on an `end` projection
/// that observes the end as the answer states it (no `compare`, `views`, `observer` or
/// `channels`): kink-flow holds an implementation's observed value only as its answer states it,
/// and narrowing its cells or applying functions of their values is the front end's comparison,
/// which states no value to store; a trace's elements are compared by the front end alone.
fn relation(
    entry: &toml::Table,
    prefix: &str,
    kind: ProjectionKind,
) -> Result<Relation, ManifestError> {
    let key = join(prefix, "relation");
    match entry.get("relation") {
        None => return Ok(Relation::Definition),
        Some(Value::String(relation)) if relation == "snapshot" => {}
        Some(Value::String(relation)) => {
            return Err(ManifestError::new(
                key,
                format!(
                    "`{relation}` is no relation: `snapshot` (an implementation's value against \
                     the one accepted for the case); leave `relation` out to compare each side \
                     with the definition"
                ),
            ));
        }
        Some(_) => return Err(ManifestError::new(key, "expected a string")),
    }
    if kind == ProjectionKind::Trace {
        return Err(ManifestError::new(
            key,
            "a `trace` projection has no snapshot: its elements are compared by the front end at \
             equal indices, and no value of them is stored; a snapshot is an `accepts` \
             projection's (the implementation's answer: accepted, rejected, crashed) or an `end` \
             projection's (the end as \
             the answer states it)",
        ));
    }
    if let Some(other) = ["compare", "views", "observer", "channels"]
        .into_iter()
        .find(|other| entry.contains_key(*other))
    {
        return Err(ManifestError::new(
            join(prefix, other),
            "a snapshot of an end holds the end as the implementation's answer states it, every \
             cell it states: narrowing the cells or comparing functions of their values is the \
             front end's comparison with the definition, which states no value to store",
        ));
    }
    Ok(Relation::Snapshot)
}

fn no_kind(prefix: &str, what: &str) -> ManifestError {
    ManifestError::new(
        join(prefix, "kind"),
        format!("{what}: `end` (the default), `accepts` or `trace`"),
    )
}

/// Every channel of `channels` is one of `observe`'s, and there is one.
fn channels_declared(
    channels: &[String],
    prefix: &str,
    observe: Option<&ObserveSection>,
) -> Result<(), ManifestError> {
    let key = join(prefix, "channels");
    if channels.is_empty() {
        return Err(ManifestError::new(
            key,
            "names no channel: a projection compares the channels of [observe] it names",
        ));
    }
    let Some(observe) = observe else {
        return Err(ManifestError::new(
            key,
            "names channels of [observe], and the flow declares none: declare [[observe.point]] \
             or [[observe.log]]",
        ));
    };
    let declared = observe.channel_names().collect::<Vec<_>>();
    if let Some((index, channel)) = channels
        .iter()
        .enumerate()
        .find(|(_, channel)| !declared.contains(&channel.as_str()))
    {
        return Err(ManifestError::new(
            format!("{key}[{index}]"),
            format!(
                "`{channel}` is no channel of [observe] (its channels: {})",
                declared
                    .iter()
                    .map(|name| format!("`{name}`"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A program with `id`, a case of the document `case` where given.
    fn program(id: &str, case: Option<&str>) -> Program {
        Program {
            id: id.to_owned(),
            source: None,
            start_sort: None,
            variables: Vec::new(),
            inputs: toml::Table::new(),
            case: case.map(str::to_owned),
            case_file: None,
            expect: None,
            expect_for: super::super::ExpectFor::default(),
            provenance: None,
            rejected: None,
            stop_count: None,
        }
    }

    fn within(domain: &[&str]) -> ProjectionSection {
        ProjectionSection {
            domain: Some(domain.iter().map(|pattern| (*pattern).to_owned()).collect()),
            ..default_projection(None)
        }
    }

    /// A domain holds a program whose id one of its patterns matches, or whose case document's
    /// path it matches: a pattern written as a `[[program]] cases` entry holds that document's
    /// named cases; a pattern of a named case's id holds that case alone.
    #[test]
    fn a_domain_holds_the_programs_its_patterns_match() {
        let listed = program("sum", None);
        let file = program("cases/io/read.imp", None);
        let single = program("cases/static/bad.toml", Some("cases/static/bad.toml"));
        let named = program("cases/static/many.toml#b", Some("cases/static/many.toml"));
        let other = program("cases/static/many.toml#c", Some("cases/static/many.toml"));
        let every = default_projection(None);
        for program in [&listed, &file, &single, &named, &other] {
            assert!(every.holds(program), "{}", program.id);
        }
        let io = within(&["cases/io/**"]);
        assert_eq!(
            [&listed, &file, &single, &named].map(|program| io.holds(program)),
            [false, true, false, false]
        );
        let documents = within(&["cases/static/*.toml", "sum"]);
        assert_eq!(
            [&listed, &file, &single, &named, &other].map(|program| documents.holds(program)),
            [true, false, true, true, true]
        );
        let one = within(&["cases/static/*.toml#b"]);
        assert_eq!(
            [&single, &named, &other].map(|program| one.holds(program)),
            [false, true, false]
        );
    }

    #[test]
    fn a_domain_pattern_that_matches_no_program_is_refused() {
        let programs = [program("sum", None), program("cases/a.imp", None)];
        let projections = [within(&["sum"]), within(&["cases/*.imp", "cases/*.k"])];
        let error = domains_hold(&projections, &programs).unwrap_err();
        assert_eq!(error.key, "projection[1].domain[1]", "{error}");
        assert!(error.message.contains("\"cases/*.k\""), "{error}");
        assert_eq!(domains_hold(&projections[..1], &programs), Ok(()));
        assert_eq!(domains_hold(&[default_projection(None)], &[]), Ok(()));
    }
}
