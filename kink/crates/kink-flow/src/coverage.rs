//! `coverage`: what the corpus covers of the obligations the specification states, family by
//! family, each obligation covered or open, and each open one stated as a target an agent can
//! act on (README, "kink-flow coverage").
//!
//! An obligation is an item derived from the definition alone, before any program runs, so each
//! family's universe is a function of the definition and the document states its size. An
//! obligation is covered when the cached baseline run of some comparable program shows the
//! family's predicate ([`crate::results`], the result cache): a program that cannot be compared
//! can kill nothing, so it tests nothing, and an item only such programs touch lists them as
//! `touched_only_by`, its target then being to make one comparable. Coverage of a family is set
//! arithmetic over the records, so adding a program runs that program alone.
//!
//! # Families
//!
//! - `rules`: every authored rewrite rule and function equation (`owise`, `anywhere` and the
//!   authored equations of an overloaded function included). An item's status is named for the
//!   predicate it tests ([`FIRED`], [`MATCHED`], [`UNMATCHED`]), read from the records as the
//!   result cache keeps them, or from the front end's reading where it reads a sentence's match
//!   at its own level (`krs.status`); a rule is covered when it is `fired`. Simplification,
//!   `symbolic` and ceil equations are [`OUT_OF_SCOPE`]: they state facts of the definition's
//!   functions that the definition means the same without, so no program's run of one tests
//!   anything a step computes. A claim helper ([`CLAIM_HELPER`]) serves the claims, which a
//!   proof checks, and a rule k-rust's coverage cannot name ([`NO_COVERAGE_SIGNAL`]) cannot be
//!   shown matched; neither is an obligation. The measure is fired / (fired + matched +
//!   unmatched).
//! - `requirements`: for each guarded rule of the rules universe whose condition has an
//!   authored conjunct, each distinct (node, truth) pair of the condition's root and of each
//!   authored operand node with outcomes of its own (an atom, or an exclusive connective;
//!   [`crate::guards::own_outcomes`]): the root `held` and `refuted`, a node `true` and `false`.
//!   A node's truth is covered when some comparable program reached the node with that truth, a
//!   node being reached, in written order, only where the operands before it decide nothing yet
//!   (a conjunction's earlier operands `true`, a disjunction's `false`); so the reached truths
//!   per node encode the short-circuit outcome classes of every connective, and one unit serves
//!   them all. Where the root's truth is reached exactly where a node is reached with a truth (a
//!   root that is itself an atom, a conjunction's `held` and its last conjunct `true`, a
//!   condition's only conjunct), the two are one obligation, listed once as the root's, with
//!   the node (`node`, `node_truth`) and the programs of both. Undefined and undecided outcomes,
//!   the tests a front end inserted and a pattern's templates are shown apart and never counted.
//!   Where a front end grouped a guard by its own constructs (`guard.krs`), its authored operands
//!   and its reading of the author's condition are read; a condition with no authored conjunct
//!   states no requirement. The nodes are read from the definition's skeleton of the condition
//!   ([`crate::guards::row_guard`]), so the universe does not depend on which programs entered
//!   it; a condition whose skeleton cannot be read shows no node and says why
//!   (`guard.operands_reason`), its requirements being its root's alone.
//! - `syntax`, `rule_windows` and `syntax_paths` are not built; each is `null`.
//! - `flips` (tier 2, condition flips) needs a front end that gives coverage the flips it
//!   generates and judges, which no front end of this build does: the family has `run: false`
//!   and the reason.
//!
//! The measure is per family. No weighted total is given, since nothing weighs a rule against an
//! operand's truth; `summary.open`, the count of open obligations, is the one scalar, and zero
//! means done. Every item has a stable `id`: `rule:<name>` and `requirement:<name>:<detail>`,
//! the rule's name being its KRS item where the front end named it, else its label, else its
//! `file:line` (with `:<label>` added where two rules share a name), and the detail `held`,
//! `refuted`, or the node's text (with `@<path>` added where two nodes of one condition share a
//! text) and its truth.
//!
//! # Targets
//!
//! One per open obligation, in tier, family, then sentence order: `{family, item, text, file,
//! line, programs, pattern, fuzz}`. An `unmatched` rule asks for a case whose run reaches a state
//! the rule matches; a `matched` one for a case that enters it with its condition holding,
//! naming the requirement that is open; a requirement for a case that enters the rule with the
//! valuation that reaches the node with the missing truth, read from the condition's structure.
//! `programs` are the comparable programs that entered the rule, the templates of a fuzz job;
//! `fuzz` spells the fuzz job that looks for a program for a rewrite rule (`--matched`,
//! `--fired`), `null` where none applies. `pattern` is, for an `unmatched` rewrite rule, its
//! left-hand side as a `PATTERNS.toml` pattern ([`rule_pattern`]), which `query` and
//! `fuzz --pattern` take; `null` for every other target, and where the rule's text cannot be
//! read or a front end matched the sentence through templates.
//!
//! The derived part of the document (every family but the rules' items, the targets and the
//! summary) is a function of the rules' items as the front end annotated them ([`derive`]), so a
//! front end that names rules and groups guards at its own level has its names in every id,
//! target and count.

use crate::{
    admit::admit_spec,
    cli::{CommandSpelling, Verb},
    digest::ExecutionDigest,
    evidence::EndReader,
    manifest::FlowManifest,
    mutation::qualified_label,
    results::{
        BaselineRunner, ProgramRow, RESULT_SCHEMA_VERSION, ResultClass, cache_directory,
        data_marked, no_coverage_signal, result_cache_value, runner_refusal, sentence_value,
        update_results,
    },
};
use k_rust::{
    definition::{AttributeKey, Sentence},
    kast::Term,
};
use kink_corpus::admission::{AdmissionRecord, AdmissionRefusal};
use kink_native::execution::SolverProfile;
use kink_patch::{SentenceRef, Sha256Digest};
use serde_json::{Map, Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    path::PathBuf,
};

/// The `schema` of the coverage document.
pub const COVERAGE_SCHEMA: &str = "kink-flow-coverage";
/// The version of the coverage document: 1, the first, which replaces the results document (its
/// last version 11), whose program rows, rule rows and guard outcomes it holds.
pub const COVERAGE_VERSION: u64 = 1;

/// The status of a rule some comparable program fired.
pub const FIRED: &str = "fired";
/// The status of a rule some comparable program matched and none fired.
pub const MATCHED: &str = "matched";
/// The status of a rule no comparable program matched.
pub const UNMATCHED: &str = "unmatched";
/// The status of a simplification, `symbolic` or ceil equation: no obligation.
pub const OUT_OF_SCOPE: &str = "out-of-scope";
/// The status of a claim helper no comparable program matched: no obligation.
pub const CLAIM_HELPER: &str = "claim-helper";
/// The status of a rule none of whose compiled ids k-rust's run coverage can name: no
/// obligation.
pub const NO_COVERAGE_SIGNAL: &str = "no-coverage-signal";

/// The families of the document, in target order.
pub const FAMILIES: [&str; 6] = [
    "rules",
    "requirements",
    "syntax",
    "rule_windows",
    "syntax_paths",
    "flips",
];

/// Why the flips family runs nothing in this build.
pub const FLIPS_NOT_BUILT: &str = "condition flips need a front end that gives coverage the \
     flips it generates, each judged as a mutation of the specification, which no front end of \
     this build does";

/// The tiers a `coverage` command computes. Tier 2's one family, condition flips, needs a front
/// end that gives coverage the flips it generates, each judged as a mutation, which no front end
/// of this build does, so tier 1 is the only one: a document states only tiers it computed.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Tier {
    /// `--tier 1` (the default): the families read from the baseline runs alone.
    #[default]
    One,
}

impl Tier {
    fn tiers(self) -> Value {
        match self {
            Self::One => json!([1]),
        }
    }
}

/// Options of the `coverage` command.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct CoverageOptions {
    /// Re-run every program that has a current record and compare (README 5.3).
    pub verify: bool,
    /// The cache directory; default `<directory of FLOW.toml>/.kink-flow`.
    pub cache: Option<PathBuf>,
    /// The tiers asked for.
    pub tier: Tier,
}

/// The refusal of a `[coverage]` value this build cannot honour, or `None`: a depth above 1
/// (rule windows and syntax paths are not built) and an `mcdc` list (unique-cause obligations are
/// not built). It is given before the specification is admitted, so nothing runs.
fn unsupported(manifest: &FlowManifest) -> Option<AdmissionRefusal> {
    let section = &manifest.coverage;
    let refusal = |reason: &str, detail: String| AdmissionRefusal {
        stage: "coverage".into(),
        reason: reason.into(),
        detail,
    };
    if section.depth.get() > 1 {
        return Some(refusal(
            "depth-unsupported",
            format!(
                "[coverage] depth = {}: this build counts single items only (depth 1); the \
                 families of sequences (rule windows, syntax paths) are not built",
                section.depth
            ),
        ));
    }
    if !section.mcdc.is_empty() {
        return Some(refusal(
            "mcdc-unsupported",
            format!(
                "[coverage] mcdc names {}: unique-cause obligations are not built; remove the \
                 key",
                section.mcdc.join(", ")
            ),
        ));
    }
    None
}

/// `kink-flow coverage`: the coverage document and whether the command found no corpus or
/// infrastructure error; the exit status joins it with the status the document gives
/// (`crate::cli::coverage_status`). The derived part ([`derive`]) is left for the caller to add
/// once a front end has annotated the rules, `spelling` saying how its fuzz jobs are spelled.
pub fn coverage(manifest: &FlowManifest, options: &CoverageOptions) -> (Value, bool) {
    // Every document names the stop, a refused specification's too, as `check` and `run` do.
    let stopped = |mut document: Value| {
        if let Some(stop) = manifest.stop_value() {
            document["stop"] = stop;
        }
        document
    };
    let settings = settings(manifest, options);
    let refused = |record: &AdmissionRecord| {
        stopped(document(
            record,
            None,
            settings.clone(),
            Vec::new(),
            None,
            Vec::new(),
            Value::Null,
        ))
    };
    if let Some(refusal) = unsupported(manifest) {
        let mut record = AdmissionRecord::new(crate::admit::SPEC_RECORD_NAME);
        record.refusal = Some(refusal);
        return (refused(&record), false);
    }
    let (mut record, admitted) = admit_spec(manifest);
    let Some((spec, mut inputs)) = admitted else {
        return (refused(&record), false);
    };
    let mut inputs = inputs.session(&spec);
    let cache = cache_directory(manifest, options.cache.as_deref());
    let runner = match BaselineRunner::new(&spec, manifest) {
        Ok(runner) => runner,
        Err(e) => {
            record.refusal = Some(runner_refusal(e));
            return (refused(&record), false);
        }
    };
    let update = update_results(
        &spec,
        manifest,
        &mut inputs,
        &runner,
        &cache,
        options.verify,
        None,
    );
    let ok = update.ok();
    let items = rule_items(&spec, manifest, &update.rows);
    let execution: ExecutionDigest = update.execution;
    let programs = data_marked(
        update.rows.into_iter().map(|row| row.row).collect(),
        &spec.data,
    );
    let mut document = stopped(document(
        &record,
        Some(update.spec_digest),
        settings,
        programs,
        Some(items),
        update.mismatches,
        runner.baseline_runs(),
    ));
    document["spec"]["execution_digest"] = execution.value();
    document["result_cache"] = result_cache_value(manifest.budget.backend_options());
    document["data"] = spec.data.value();
    document["result"] = spec.result.value();
    document["spec"]["exclusion"] = runner.definition_exclusion();
    document["spec"]["short_circuit"] = runner.short_circuit();
    (document, ok)
}

/// The document's `settings`: the tiers computed, `[coverage]`'s values, and whether the
/// manifest declared them (`source`).
fn settings(manifest: &FlowManifest, options: &CoverageOptions) -> Value {
    let section = &manifest.coverage;
    json!({
        "tiers": options.tier.tiers(),
        "depth": section.depth.get(),
        "mcdc": section.mcdc,
        "max_obligations": section.max_obligations.get(),
        "source": if section.declared { "manifest" } else { "default" },
    })
}

/// Whether `sentence` is out of the rules universe ([`OUT_OF_SCOPE`]): a simplification, a
/// `symbolic` equation, or an equation whose left-hand side is a `#Ceil`.
fn out_of_scope(sentence: &Sentence) -> bool {
    let Sentence::Rule {
        body, attributes, ..
    } = sentence
    else {
        return false;
    };
    attributes.has(AttributeKey::Simplification)
        || attributes.has(AttributeKey::Symbolic)
        || ceil_left_side(body)
}

/// Whether a rule's body rewrites a `#Ceil` application at its top.
fn ceil_left_side(body: &Term) -> bool {
    match body {
        Term::Annotated { term, .. } => ceil_left_side(term),
        Term::Rewrite { left, .. } => ceil_left_side(left),
        Term::Apply { label, .. } => label.name == "#Ceil",
        _ => false,
    }
}

/// The left-hand side of a rule as K text, a pattern `query` and `fuzz --pattern` take
/// (README, "PATTERNS.toml"): the text of its body as written, each rewrite replaced by the text
/// of its left side, without its `requires`, and each variable written without a sort given the
/// sort the rule's parse inferred for it. A pattern denotes the configurations its left side
/// matches and refuses a variable that occurs only on a rewrite's right side, so the right sides
/// are left out; the sorts keep what the right side and the condition told the parse about the
/// variables, so the pattern matches what the rule's left-hand side matches. `text` is the
/// rule's text in its file's K view, starting at byte `start` of that view, which the spans of
/// the rule's terms index. `None` where a term the text needs has no span inside the rule's text.
fn left_side_text(sentence: &Sentence, text: &str, start: usize) -> Option<String> {
    use k_rust::kast::TermSpan;
    use std::ops::Range;
    type Edits = Vec<(Range<usize>, String)>;
    let slice = |range: Range<usize>| -> Option<&str> {
        text.get(range.start.checked_sub(start)?..range.end.checked_sub(start)?)
    };
    // A term's span: its annotation's, or, for a cast the parse inserted (which has none), its
    // variable's.
    fn span(term: &Term) -> Option<TermSpan> {
        match term {
            Term::Annotated { term, metadata } => metadata.span.or_else(|| span(term)),
            Term::Apply { label, arguments } if label.semantic_cast_sort().is_some() => {
                match arguments.as_slice() {
                    [argument] => span(argument),
                    _ => None,
                }
            }
            _ => None,
        }
    }
    // `range` of the text with `edits` (sorted, disjoint, inside it) applied.
    let apply = |range: Range<usize>, mut edits: Edits| -> Option<String> {
        edits.sort_by_key(|(at, _)| at.start);
        let mut out = String::new();
        let mut at = range.start;
        for (edited, replacement) in edits {
            if edited.start < at || edited.end > range.end {
                return None;
            }
            out.push_str(slice(at..edited.start)?);
            out.push_str(&replacement);
            at = edited.end;
        }
        out.push_str(slice(at..range.end)?);
        Some(out)
    };
    // The edits of `term`, `around` the span of the annotation directly around it.
    fn edits<'t>(
        term: &Term,
        around: Option<TermSpan>,
        apply: &dyn Fn(Range<usize>, Edits) -> Option<String>,
        slice: &dyn Fn(Range<usize>) -> Option<&'t str>,
        found: &mut Edits,
    ) -> Option<()> {
        match term {
            Term::Annotated { term, metadata } => {
                edits(term, metadata.span.or(around), apply, slice, found)
            }
            Term::Rewrite { left, .. } => {
                // A span ends after the layout that follows it: the rewrite's is kept, after the
                // left side's text.
                let whole = around?;
                let left_span = span(left)?;
                let mut inner = Vec::new();
                edits(left, None, apply, slice, &mut inner)?;
                let rendered = apply(left_span.start..left_span.end, inner)?;
                let written = slice(whole.start..whole.end)?;
                let layout = &written[written.trim_end().len()..];
                found.push((
                    whole.start..whole.end,
                    format!("{}{layout}", rendered.trim_end()),
                ));
                Some(())
            }
            Term::Variable {
                name,
                sort: Some(sort),
            } => {
                if let Some(at) = around {
                    let written = slice(at.start..at.end)?;
                    if written.trim_end() == name {
                        let end = at.start + written.trim_end().len();
                        found.push((end..end, format!(":{sort}")));
                    }
                }
                Some(())
            }
            // The parse states a variable's inferred sort as a cast around it.
            Term::Apply { label, arguments }
                if label.semantic_cast_sort().is_some()
                    && matches!(
                        arguments.as_slice(),
                        [argument] if matches!(argument.unannotated(), Term::Variable { .. })
                    ) =>
            {
                let (Some(sort), [argument]) = (label.semantic_cast_sort(), arguments.as_slice())
                else {
                    return Some(());
                };
                // A cast the parse inserted has no span of its own; its variable has.
                let Some(at) = around.or_else(|| span(argument)) else {
                    return Some(());
                };
                let Term::Variable { name, .. } = argument.unannotated() else {
                    return Some(());
                };
                let written = slice(at.start..at.end)?;
                if written.trim_end() == name {
                    let end = at.start + written.trim_end().len();
                    found.push((end..end, format!(":{sort}")));
                }
                Some(())
            }
            Term::As { pattern, alias } => {
                edits(pattern, None, apply, slice, found)?;
                edits(alias, None, apply, slice, found)
            }
            Term::Apply { arguments, .. } | Term::Sequence(arguments) => arguments
                .iter()
                .try_for_each(|argument| edits(argument, None, apply, slice, found)),
            Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => Some(()),
        }
    }
    let Sentence::Rule { body, .. } = sentence else {
        return None;
    };
    let whole = span(body)?;
    let mut found = Vec::new();
    edits(body, None, &apply, &slice, &mut found)?;
    let pattern = apply(whole.start..whole.end, found)?;
    let pattern = pattern.trim();
    (!pattern.is_empty()).then(|| pattern.to_owned())
}

/// The cells of a definition's configuration, as far as a rule's left-hand side as a pattern
/// needs them ([`rule_pattern`]): every cell's label, and the main cell's tokens.
struct Cells {
    labels: BTreeSet<String>,
    /// The main cell's opening and closing tokens, where the configuration has exactly one.
    main: Option<(String, String)>,
}

impl Cells {
    fn of(definition: &k_rust::definition::Definition) -> Self {
        use k_rust::definition::ProductionItem;
        let mut labels = BTreeSet::new();
        let mut mains = BTreeSet::new();
        for module in &definition.modules {
            for sentence in &module.local_sentences {
                let Sentence::Production {
                    label: Some(label),
                    items,
                    attributes,
                    ..
                } = &**sentence
                else {
                    continue;
                };
                if !attributes.has(AttributeKey::Cell) {
                    continue;
                }
                labels.insert(label.name.clone());
                if attributes.has(AttributeKey::Maincell) {
                    let terminals = items
                        .iter()
                        .filter_map(|item| match item {
                            ProductionItem::Terminal(token) => Some(token.clone()),
                            _ => None,
                        })
                        .collect::<Vec<_>>();
                    if let [open, close] = terminals.as_slice() {
                        mains.insert((open.clone(), close.clone()));
                    }
                }
            }
        }
        let main = (mains.len() == 1)
            .then(|| mains.into_iter().next())
            .flatten();
        Self { labels, main }
    }

    /// The items of a body as the configuration's cells read it: the operands of the internal
    /// joins of cells, else the body.
    fn items(term: &Term) -> Vec<&Term> {
        match term.unannotated() {
            Term::Apply { label, arguments } if label.is(k_rust::kast::InternalLabel::Cells) => {
                arguments.iter().flat_map(Self::items).collect()
            }
            _ => vec![term],
        }
    }

    fn cell(&self, term: &Term) -> bool {
        matches!(term.unannotated(), Term::Apply { label, .. } if self.labels.contains(&label.name))
    }

    /// Whether the compile places the body of `sentence`, a rewrite rule, in the main cell: a
    /// rule that is not macro-like, `anywhere` or a simplification, whose body is one item that
    /// is not a cell and, for a rewrite, whose sides hold no cell. Its left-hand side then
    /// matches at the head of the main cell's contents.
    fn wrapped(&self, sentence: &Sentence) -> bool {
        let Sentence::Rule {
            body, attributes, ..
        } = sentence
        else {
            return false;
        };
        if attributes.has_any(&AttributeKey::MACRO_LIKE)
            || attributes.has(AttributeKey::Anywhere)
            || attributes.has(AttributeKey::Simplification)
        {
            return false;
        }
        match Self::items(body).as_slice() {
            [item] if !self.cell(item) => match item.unannotated() {
                Term::Rewrite { left, right } => Self::items(left)
                    .into_iter()
                    .chain(Self::items(right))
                    .all(|term| !self.cell(term)),
                _ => true,
            },
            _ => false,
        }
    }
}

/// A rewrite rule's left-hand side as a pattern ([`left_side_text`]), placed at the head of the
/// main cell where the compile places the rule there ([`Cells::wrapped`]), since a pattern's cells
/// are completed but a pattern with none is not placed in one. `None` where the text cannot be
/// read, or the rule is placed in a main cell the configuration does not single out.
fn rule_pattern(sentence: &Sentence, text: &str, start: usize, cells: &Cells) -> Option<String> {
    let left = left_side_text(sentence, text, start)?;
    if cells.wrapped(sentence) {
        let (open, close) = cells.main.as_ref()?;
        Some(format!("{open} {left} ...{close}"))
    } else {
        Some(left)
    }
}

/// Every authored rule of the specification, in sentence order, as the rules family's items
/// before [`derive`]: its position ([`sentence_value`]), its status, the comparable programs
/// whose coverage matches it (`matched_by`, k-rust `matched`) and fires it (`fired_by`: for a
/// rewrite rule k-rust `committed`, some path of the run takes the rule's step; for an equation
/// k-rust `applied`, an instance gave a result), whether it compiles to a rewrite rule
/// (`rewrite`), the programs that are not comparable and match or fire it (`uncounted`), the
/// outcomes of its guard ([`crate::guards::row_guard`]), and, for an `unmatched` rewrite rule,
/// its left-hand side as a pattern (`pattern`, [`left_side_text`]; `null` otherwise).
///
/// The statuses partition the rules with the precedence [`OUT_OF_SCOPE`],
/// [`NO_COVERAGE_SIGNAL`], [`FIRED`], [`MATCHED`], [`CLAIM_HELPER`], [`UNMATCHED`]; firing
/// implies matching. A claim helper (`FlowManifest::claim_helpers`) is an equation of a function
/// only claims apply: no program text reaches it, but no program text reaches a function nothing
/// applies either, and such a sentence stays `unmatched`, since neither a run nor a claim accounts
/// for it; a typed input can still apply any function, so a claim helper some comparable program
/// matched or fired has that status.
fn rule_items(
    spec: &crate::admit::AdmittedSpec,
    manifest: &FlowManifest,
    rows: &[ProgramRow],
) -> Vec<Value> {
    type Lists<'p> = BTreeMap<(String, u64), Vec<&'p str>>;
    let mut lists: [Lists<'_>; 4] = Default::default();
    let mut comparable = Vec::new();
    let mut others = Vec::new();
    for (program, row) in manifest.programs.iter().zip(rows) {
        let Some(record) = &row.record else {
            continue;
        };
        let counted = record["class"] == ResultClass::Comparable.as_str();
        if counted {
            comparable.push((program.id.as_str(), record));
        } else {
            others.push((program.id.as_str(), record));
        }
        let offset = if counted { 0 } else { 2 };
        for (key, slot) in [("sentences", offset), ("fired_sentences", offset + 1)] {
            for sentence in record["coverage"][key].as_array().into_iter().flatten() {
                if let (Some(module), Some(index)) =
                    (sentence["module"].as_str(), sentence["index"].as_u64())
                {
                    lists[slot]
                        .entry((module.to_owned(), index))
                        .or_default()
                        .push(&program.id);
                }
            }
        }
    }
    let [matched, fired, others_matched, others_fired] = lists;
    let guards = crate::guards::SentenceGuards::of(comparable.iter().copied());
    let other_guards = crate::guards::SentenceGuards::of(others.iter().copied());
    let printer = EndReader::of(&spec.compiled);
    let no_signal = no_coverage_signal(spec);
    let rewrites = crate::fuzz::rewrite_ids(&spec.compiled);
    let authors = kink_native::coverage::RuleAuthors::of(&spec.compiled);
    let claim_helpers = manifest
        .claim_helpers
        .iter()
        .map(|(module, label)| qualified_label(label, module))
        .collect::<BTreeSet<_>>();
    let texts = crate::mutation::rule_texts(manifest, &spec.loaded)
        .into_iter()
        .filter_map(|rule| Some(((rule.at.module, rule.at.index), (rule.text?, rule.start?))))
        .collect::<BTreeMap<_, _>>();
    let cells = Cells::of(spec.loaded.baseline.definition());
    let mut items = Vec::new();
    for (at, sentence) in spec.loaded.baseline.authored_sentences() {
        let Sentence::Rule {
            requires,
            attributes,
            ..
        } = sentence
        else {
            continue;
        };
        let mut value = sentence_value(spec, &at);
        let key = (at.module.clone(), u64::from(at.index));
        let list = |lists: &Lists<'_>| -> Vec<String> {
            lists
                .get(&key)
                .into_iter()
                .flatten()
                .map(|program| (*program).to_owned())
                .collect()
        };
        let (programs, firing) = (list(&matched), list(&fired));
        let claim_helper = attributes
            .string(AttributeKey::Label)
            .is_some_and(|label| claim_helpers.contains(&qualified_label(label, &at.module)));
        let status = if out_of_scope(sentence) {
            OUT_OF_SCOPE
        } else if no_signal.contains_key(&at) {
            NO_COVERAGE_SIGNAL
        } else if !firing.is_empty() {
            FIRED
        } else if !programs.is_empty() {
            MATCHED
        } else if claim_helper {
            CLAIM_HELPER
        } else {
            UNMATCHED
        };
        value["status"] = json!(status);
        value["matched_by"] = json!(programs);
        value["fired_by"] = json!(firing);
        let rewrite = authors.ids_of(&at).any(|id| rewrites.contains(id));
        value["rewrite"] = json!(rewrite);
        value["pattern"] = json!(
            (rewrite && status == UNMATCHED)
                .then(|| texts.get(&(at.module.clone(), at.index)))
                .flatten()
                .and_then(|(text, start)| rule_pattern(sentence, text, *start, &cells))
        );
        value["uncounted"] = json!({
            "matched_by": list(&others_matched),
            "fired_by": list(&others_fired),
        });
        if !crate::guards::unconditional(requires) && matches!(status, FIRED | MATCHED | UNMATCHED)
        {
            let at_ref = SentenceRef {
                module: at.module.clone(),
                index: at.index,
            };
            let skeletons = match &spec.guard_skeletons {
                Ok(skeletons) => match skeletons.unreadable.get(&at_ref) {
                    Some(reason) => Err(reason.as_str()),
                    None => Ok(skeletons
                        .by_sentence
                        .get(&at_ref)
                        .map(|skeletons| crate::guards::skeleton_values(skeletons))
                        .unwrap_or_default()),
                },
                Err(reason) => Err(reason.as_str()),
            };
            value["guard"] = crate::guards::row_guard(
                guards.get(&key),
                other_guards.get(&key),
                skeletons.as_deref().map_err(|reason| *reason),
                &printer,
            );
        }
        if let Some(reason) = no_signal.get(&at) {
            value["reason"] = json!(reason);
        } else if status == OUT_OF_SCOPE {
            value["reason"] = json!(
                "a simplification, symbolic or ceil equation states a fact of the definition's \
                 functions, which the definition means the same without: no step computes it"
            );
        }
        items.push(value);
    }
    items
}

/// The coverage document before [`derive`]: `rules` are the rules family's items, `None` for a
/// refused specification (every family is then `null`).
fn document(
    record: &AdmissionRecord,
    digest: Option<Sha256Digest>,
    settings: Value,
    programs: Vec<Value>,
    rules: Option<Vec<Value>>,
    mismatches: Vec<Value>,
    baseline_runs: Value,
) -> Value {
    let refusal = record.refusal.as_ref();
    let families = rules.map_or(
        Value::Null,
        |items| json!({"rules": {"tier": 1, "items": items}}),
    );
    // Under the Z3 profile `z3`, the Z3 build the classes were decided on
    // (`crate::with_z3_build`), which the verdicts rendering names.
    crate::with_z3_build(json!({
        "schema": COVERAGE_SCHEMA,
        "version": COVERAGE_VERSION,
        "k_rust_revision": crate::k_rust_revision(),
        "profile": SolverProfile::BUILD.name(),
        "result_schema_version": RESULT_SCHEMA_VERSION,
        "spec": {
            "outcome": if refusal.is_some() { "refused" } else { "admitted" },
            "stage": refusal.map(|r| &r.stage),
            "reason": refusal.map(|r| &r.reason),
            "detail": refusal.map(|r| &r.detail),
            "digest": digest.map(|d| d.to_string()),
            "files": record
                .files
                .iter()
                .map(|f| json!({"name": f.name, "sha256": f.sha256.to_string()}))
                .collect::<Vec<_>>(),
            // The definition exclusion and the rules the short-circuit analysis flags
            // (`crate::exclusion`), set once the specification is admitted.
            "exclusion": null,
            "short_circuit": null,
        },
        "settings": settings,
        "programs": programs,
        "families": families,
        "targets": [],
        "summary": null,
        "mismatches": mismatches,
        "baseline_runs": baseline_runs,
        "data": null,
        "result": null,
    }))
}

/// A rule item's name: its KRS item where a front end named it (`krs.item`), its label, or its
/// `file:line` (`module#index` without a file).
#[must_use]
pub fn rule_name(rule: &Value) -> String {
    if let Some(item) = rule["krs"]["item"].as_str() {
        return item.to_owned();
    }
    if let Some(label) = rule["label"].as_str() {
        return label.to_owned();
    }
    match (rule["file"].as_str(), rule["start_line"].as_u64()) {
        (Some(file), Some(line)) => format!("{file}:{line}"),
        _ => format!(
            "{}#{}",
            rule["module"].as_str().unwrap_or_default(),
            rule["index"]
        ),
    }
}

/// A rule item's status: the front end's (`krs.status`, which reads a sentence's match at its own
/// level) where it gave one, else kink-flow's.
#[must_use]
pub fn rule_status(rule: &Value) -> Option<&str> {
    rule["krs"]["status"]
        .as_str()
        .or_else(|| rule["status"].as_str())
}

/// The program ids of a JSON list, each a string or a `{program}` object.
fn ids(value: &Value) -> Vec<String> {
    value
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|entry| entry.as_str().or_else(|| entry["program"].as_str()))
        .map(str::to_owned)
        .collect()
}

/// `programs` without the ones `covered` already lists, in their order, each once.
fn without(programs: Vec<String>, covered: &[String]) -> Vec<String> {
    let mut kept = Vec::new();
    for program in programs {
        if !covered.contains(&program) && !kept.contains(&program) {
            kept.push(program);
        }
    }
    kept
}

/// Where a target or a requirement points: the KRS position where a front end named the rule,
/// else the K one.
fn position(rule: &Value) -> (Value, Value) {
    let krs = &rule["krs"];
    if krs["file"].is_string() {
        (krs["file"].clone(), krs["line"].clone())
    } else {
        (rule["file"].clone(), rule["start_line"].clone())
    }
}

/// A family's measure: covered / obligations, `null` without obligations.
fn measure(covered: usize, obligations: usize) -> Value {
    if obligations == 0 {
        Value::Null
    } else {
        let ratio = covered as f64 / obligations as f64;
        json!(ratio)
    }
}

/// The display tree of a guard (`guard.operands`), by path.
struct Tree<'g> {
    operands: BTreeMap<&'g str, &'g Value>,
}

impl<'g> Tree<'g> {
    fn of(guard: &'g Value) -> Self {
        Self {
            operands: guard["operands"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(|operand| Some((operand["path"].as_str()?, operand)))
                .collect(),
        }
    }

    fn parent(path: &str) -> Option<&str> {
        path.rsplit_once('.').map(|(parent, _)| parent)
    }

    /// Whether the node at `path` is a front end's insertion or a template's conjunct, not the
    /// author's (`krs.origin` other than `authored`).
    fn generated(&self, path: &str) -> bool {
        self.operands.get(path).is_some_and(|operand| {
            operand["krs"]["origin"]
                .as_str()
                .is_some_and(|origin| origin != "authored")
        })
    }

    /// The text of the node at `path` as an author reads it: an atom's own text (`krs.text`,
    /// else its K text), a connective's operands joined by its token, leaving out what a front
    /// end inserted; `None` for a node with nothing of the author's.
    fn text(&self, path: &str) -> Option<String> {
        let operand = self.operands.get(path)?;
        if self.generated(path) && operand["kind"] == "atom" {
            return None;
        }
        let own = operand["krs"]["text"]
            .as_str()
            .or_else(|| operand["text"].as_str());
        let children = operand["operands"].as_array();
        let Some(children) = children.filter(|_| operand["kind"] != "atom") else {
            return own.map(str::to_owned);
        };
        let token = operand["krs"]["text"]
            .as_str()
            .or_else(|| operand["connective"].as_str())
            .unwrap_or_default();
        let parts = children
            .iter()
            .filter_map(Value::as_str)
            .filter_map(|child| {
                let text = self.text(child)?;
                let nested = self
                    .operands
                    .get(child)
                    .is_some_and(|c| c["kind"] != "atom");
                Some(if nested { format!("({text})") } else { text })
            })
            .collect::<Vec<_>>();
        match parts.as_slice() {
            [] => None,
            [one] if matches!(operand["kind"].as_str(), Some("negation")) => {
                Some(format!("{token}{one}"))
            }
            [one] => Some(one.clone()),
            _ => Some(parts.join(&format!(" {token} "))),
        }
    }

    /// The truths of the author's nodes that reach the node at `path`, from the root down: a
    /// conjunction's earlier operands `true`, a disjunction's `false`, an implication's left
    /// operand `true` for its right one (the reached rule of guard outcomes).
    fn reaching(&self, path: &str) -> Vec<(String, bool)> {
        let mut chain = Vec::new();
        let mut child = path;
        while let Some(parent) = Self::parent(child) {
            if let Some(operand) = self.operands.get(parent) {
                let siblings = operand["operands"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .filter_map(Value::as_str)
                    .collect::<Vec<_>>();
                let earlier = siblings
                    .iter()
                    .take_while(|sibling| **sibling != child)
                    .copied()
                    .collect::<Vec<_>>();
                let truth = match operand["kind"].as_str() {
                    Some("conjunction") => Some(true),
                    Some("disjunction") => Some(false),
                    Some("implication") => Some(true),
                    _ => None,
                };
                if let Some(truth) = truth {
                    let mut level = earlier
                        .iter()
                        .filter_map(|sibling| Some((self.text(sibling)?, truth)))
                        .collect::<Vec<_>>();
                    level.extend(chain);
                    chain = level;
                }
            }
            child = parent;
        }
        chain
    }

    /// The author's node and truth whose reached truth is the node at `path` reached with
    /// `truth`, where there is one: the node itself for an atom or an exclusive connective (whose
    /// outcomes are their own); a negation's operand with the other truth; for `true`, a
    /// conjunction's last operand, which is reached only where every operand before it is
    /// `true`; for `false`, a disjunction's last operand, dually, and an implication's right
    /// operand, reached only where its left one is `true`. `None` where the truth is a union of
    /// several nodes' (a conjunction's `false`), or rests on a node a front end inserted.
    fn restated(&self, path: &str, truth: bool) -> Option<(String, bool)> {
        let operand = self.operands.get(path)?;
        let children = operand["operands"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .collect::<Vec<_>>();
        match (operand["kind"].as_str()?, truth) {
            ("atom" | "exclusive", _) => (!self.generated(path)).then(|| (path.to_owned(), truth)),
            ("negation", _) => match children.as_slice() {
                [one] => self.restated(one, !truth),
                _ => None,
            },
            ("conjunction", true) | ("disjunction" | "implication", false) => {
                self.restated(children.last()?, truth)
            }
            _ => None,
        }
    }

    /// Whether the node at `path` is a conjunct of the condition: every node above it is a
    /// conjunction.
    fn conjunct(&self, path: &str) -> bool {
        let mut child = path;
        while let Some(parent) = Self::parent(child) {
            if self.operands.get(parent).map(|p| &p["kind"]) != Some(&json!("conjunction")) {
                return false;
            }
            child = parent;
        }
        true
    }
}

/// One requirement node: its display path, its text, and its outcomes' lists.
struct Node {
    path: String,
    text: String,
    true_by: Vec<String>,
    false_by: Vec<String>,
    undecided_by: Vec<String>,
}

/// The requirements of one guarded rule item, `name` its name (module documentation).
fn requirements(name: &str, rule_id: &str, rule: &Value, entered: &[String]) -> Vec<Value> {
    let guard = &rule["guard"];
    if !crate::guards::authored_condition(guard) {
        return Vec::new();
    }
    let tree = Tree::of(guard);
    let grouped = &guard["krs"];
    let nodes: Vec<Node> = if grouped.is_object() {
        grouped["authored"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|node| {
                let path = node["path"].as_str().unwrap_or_default().to_owned();
                Node {
                    text: node["text"]
                        .as_str()
                        .map(str::to_owned)
                        .or_else(|| tree.text(&path))
                        .unwrap_or_else(|| path.clone()),
                    path,
                    true_by: ids(&node["true_by"]),
                    false_by: ids(&node["false_by"]),
                    undecided_by: ids(&node["undecided_by"]),
                }
            })
            .collect()
    } else {
        guard["operands"]
            .as_array()
            .into_iter()
            .flatten()
            .filter(|operand| operand.get("never").is_some())
            .map(|operand| {
                let path = operand["path"].as_str().unwrap_or_default().to_owned();
                Node {
                    text: operand["text"].as_str().unwrap_or(&path).to_owned(),
                    path,
                    true_by: ids(&operand["true_by"]),
                    false_by: ids(&operand["false_by"]),
                    undecided_by: ids(&operand["undecided_by"]),
                }
            })
            .collect()
    };
    let (held, refuted) = if grouped.is_object() {
        (ids(&grouped["held_by"]), ids(&grouped["refuted_by"]))
    } else {
        (ids(&guard["held_by"]), ids(&guard["refuted_by"]))
    };
    // The outcomes the programs that are not comparable saw, which no requirement counts.
    let uncounted = &guard["uncounted"];
    let uncounted_node = |path: &str, truth: bool| {
        ids(&uncounted["nodes"][path][if truth { "true_by" } else { "false_by" }])
    };
    let (uncounted_held, uncounted_refuted) = if grouped.is_object() {
        // The author's condition: its last authored conjunct reached true, or one reached false.
        let conjuncts = nodes
            .iter()
            .filter(|node| tree.conjunct(&node.path))
            .collect::<Vec<_>>();
        (
            conjuncts
                .last()
                .map(|node| uncounted_node(&node.path, true))
                .unwrap_or_default(),
            conjuncts
                .iter()
                .flat_map(|node| uncounted_node(&node.path, false))
                .collect(),
        )
    } else {
        (ids(&uncounted["held_by"]), ids(&uncounted["refuted_by"]))
    };
    let undecided = ids(&guard["undecided_by"]);
    let (file, line) = position(rule);
    let item = |detail: String,
                node: Option<&str>,
                truth: &str,
                text: &str,
                covered_by: Vec<String>,
                undecided_by: Vec<String>,
                touched: Vec<String>| {
        let covered = !covered_by.is_empty();
        json!({
            "id": format!("requirement:{name}:{detail}"),
            "rule": rule_id,
            "node": node,
            "truth": truth,
            "text": text,
            "file": file,
            "line": line,
            "status": if covered { "covered" } else { "open" },
            "covered": covered,
            "covered_by": covered_by,
            "undecided_by": undecided_by,
            "touched_only_by": if covered { Vec::new() } else { without(touched, &[]) },
            "entered_by": entered,
        })
    };
    // The condition's own outcomes are the root's truths. Where one of them is an operand
    // node's reached truth (`Tree::restated`), the two are one obligation: it is listed once, as
    // the root's, with the node and the programs of both.
    let conjuncts = guard["operands"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|operand| operand["path"].as_str())
        .filter(|path| {
            tree.conjunct(path)
                && tree.operands.get(path).map(|o| &o["kind"]) != Some(&json!("conjunction"))
                && !tree.generated(path)
        })
        .collect::<Vec<_>>();
    // Without a front end's grouping, the condition is every conjunct the compile wrote; only
    // where the compile added none (`compiled` empty) are the shown conjuncts all of it.
    let whole = grouped.is_object()
        || guard["compiled"]
            .as_array()
            .is_none_or(|compiled| compiled.is_empty());
    let restated = |truth: bool| -> Option<(String, bool)> {
        if !whole {
            return None;
        }
        let restated = match (truth, conjuncts.as_slice()) {
            (true, [.., last]) => tree.restated(last, true),
            (false, [one]) => tree.restated(one, false),
            _ => None,
        }?;
        nodes
            .iter()
            .any(|node| node.path == restated.0)
            .then_some(restated)
    };
    let (held_node, refuted_node) = (restated(true), restated(false));
    let reaching = |path: &str| {
        Value::Array(
            tree.reaching(path)
                .into_iter()
                .map(|(text, truth)| json!({"text": text, "truth": truth}))
                .collect(),
        )
    };
    let mut items = Vec::new();
    for (outcome, programs, uncounted_programs, restated) in [
        ("held", held, uncounted_held, &held_node),
        ("refuted", refuted, uncounted_refuted, &refuted_node),
    ] {
        let value = match restated {
            None => item(
                outcome.into(),
                None,
                outcome,
                "the condition",
                programs,
                undecided.clone(),
                uncounted_programs,
            ),
            Some((path, truth)) => {
                let node = nodes
                    .iter()
                    .find(|node| &node.path == path)
                    .expect("a restated node is a requirement node");
                let by = if *truth {
                    &node.true_by
                } else {
                    &node.false_by
                };
                let mut covered_by = programs;
                covered_by.extend(by.iter().cloned());
                let mut touched = uncounted_programs;
                touched.extend(uncounted_node(path, *truth));
                let mut undecided_by = undecided.clone();
                undecided_by.extend(node.undecided_by.iter().cloned());
                let mut value = item(
                    outcome.into(),
                    Some(path.as_str()),
                    outcome,
                    &node.text,
                    without(covered_by, &[]),
                    without(undecided_by, &[]),
                    touched,
                );
                value["node_truth"] = json!(if *truth { "true" } else { "false" });
                value["reaching"] = reaching(path);
                value
            }
        };
        items.push(value);
    }
    let mut seen = BTreeMap::<&str, usize>::new();
    for node in &nodes {
        *seen.entry(node.text.as_str()).or_default() += 1;
    }
    for node in &nodes {
        let label = if seen[node.text.as_str()] > 1 {
            format!("{}@{}", node.text, node.path)
        } else {
            node.text.clone()
        };
        for (truth, by) in [(true, &node.true_by), (false, &node.false_by)] {
            let restates = |restated: &Option<(String, bool)>| {
                restated
                    .as_ref()
                    .is_some_and(|(path, t)| *path == node.path && *t == truth)
            };
            if restates(&held_node) || restates(&refuted_node) {
                continue;
            }
            let mut value = item(
                format!("{label}:{truth}"),
                Some(&node.path),
                if truth { "true" } else { "false" },
                &node.text,
                by.clone(),
                node.undecided_by.clone(),
                uncounted_node(&node.path, truth),
            );
            value["reaching"] = reaching(&node.path);
            items.push(value);
        }
    }
    items
}

/// A list of names as a sentence reads it: `a`, `a and b`, `a, b and c`.
fn listed(names: &[String]) -> String {
    match names {
        [] => String::new(),
        [one] => one.clone(),
        [init @ .., last] => format!("{} and {last}", init.join(", ")),
    }
}

/// What a target adds for programs that touch its item and are not comparable.
fn touched_note(touched: &[String]) -> String {
    if touched.is_empty() {
        String::new()
    } else {
        format!(
            "; {} {} it but {} not comparable: make one comparable (its row's cause says why)",
            listed(touched),
            if touched.len() == 1 {
                "touches"
            } else {
                "touch"
            },
            if touched.len() == 1 { "is" } else { "are" }
        )
    }
}

/// Fill the derived part of a coverage document from its rules' items (module documentation):
/// each item's `id`, `obligation`, `covered` and `touched_only_by`, the counts and measure of
/// each family, the requirements, the targets and the summary. `spelling` spells the fuzz jobs of
/// the targets. A document whose specification was refused, or that is no coverage document, is
/// left as it is. Applying it twice gives what applying it once does.
pub fn derive(document: &mut Value, spelling: &dyn CommandSpelling) {
    if document["schema"] != COVERAGE_SCHEMA {
        return;
    }
    let programs = document["programs"].as_array().cloned().unwrap_or_default();
    let summary_programs = json!({
        "programs": programs.len(),
        "comparable": programs.iter().filter(|p| p["class"] == "comparable").count(),
        "computed": programs.iter().filter(|p| p["cached"] == false).count(),
        "mismatches": document["mismatches"].as_array().map_or(0, Vec::len),
    });
    let Some(items) = document
        .get_mut("families")
        .and_then(|families| families.get_mut("rules"))
        .and_then(|rules| rules.get_mut("items"))
        .and_then(Value::as_array_mut)
    else {
        document["summary"] = summary_programs;
        return;
    };
    // Names: a rule's name, made unique by its label where two rules share it.
    let names = items.iter().map(rule_name).collect::<Vec<_>>();
    let mut counts = BTreeMap::<&str, usize>::new();
    for name in &names {
        *counts.entry(name.as_str()).or_default() += 1;
    }
    let fuzz = spelling.command(Verb::Fuzz);
    let mut status_counts = BTreeMap::<&'static str, usize>::new();
    let mut requirement_items = Vec::new();
    let mut targets = Vec::new();
    let mut requirement_targets = Vec::new();
    for (item, name) in items.iter_mut().zip(&names) {
        let name = if counts[name.as_str()] > 1 {
            format!("{name}:{}", item["label"].as_str().unwrap_or_default())
        } else {
            name.clone()
        };
        let id = format!("rule:{name}");
        let status = rule_status(item).unwrap_or(UNMATCHED).to_owned();
        let obligation = matches!(status.as_str(), FIRED | MATCHED | UNMATCHED);
        let covered = status == FIRED;
        for known in [
            FIRED,
            MATCHED,
            UNMATCHED,
            OUT_OF_SCOPE,
            CLAIM_HELPER,
            NO_COVERAGE_SIGNAL,
        ] {
            if status == known {
                *status_counts.entry(known).or_default() += 1;
            }
        }
        let templated = item["guard"]["krs"]["templates"].is_object();
        let mut touched = if obligation && !covered {
            ids(&item["uncounted"]["fired_by"])
        } else {
            Vec::new()
        };
        if status == UNMATCHED && !templated {
            touched.extend(ids(&item["uncounted"]["matched_by"]));
        }
        let touched = without(touched, &[]);
        item["id"] = json!(id);
        item["obligation"] = json!(obligation);
        item["covered"] = if obligation {
            json!(covered)
        } else {
            Value::Null
        };
        item["touched_only_by"] = json!(touched);
        let entered = ids(item["krs"]
            .get("matched_by")
            .filter(|_| templated)
            .unwrap_or(&item["matched_by"]));
        let (file, line) = position(item);
        let rewrite = item["rewrite"] == true;
        let rule_spelling = item["label"].as_str().map(str::to_owned).or_else(|| {
            Some(format!(
                "{}:{}",
                item["file"].as_str()?,
                item["start_line"].as_u64()?
            ))
        });
        let held_id = format!("requirement:{name}:held");
        let requirements = if obligation && item.get("guard").is_some() {
            requirements(&name, &id, item, &entered)
        } else {
            Vec::new()
        };
        if obligation && !covered {
            let (text, job) = if status == MATCHED {
                let requirement = requirements
                    .iter()
                    .any(|r| r["id"] == held_id.as_str() && r["covered"] == false);
                (
                    format!(
                        "a case where {name} is entered and its condition holds, so that its \
                         right-hand side is built on a path{}",
                        if requirement {
                            format!(" (requirement {held_id} is open)")
                        } else {
                            String::new()
                        }
                    ),
                    "--fired",
                )
            } else {
                (
                    format!("a case whose run reaches a state that {name} matches"),
                    "--matched",
                )
            };
            targets.push(json!({
                "family": "rules",
                "item": id,
                "text": format!("{text}{}", touched_note(&touched)),
                "file": file,
                "line": line,
                "programs": if status == MATCHED { entered.clone() } else { Vec::new() },
                // A front end's template-matched sentence has a bare variable as its K left-hand
                // side, so the K text is no pattern of its match.
                "pattern": if status == UNMATCHED && !templated {
                    item["pattern"].clone()
                } else {
                    Value::Null
                },
                "fuzz": match (rewrite, &rule_spelling) {
                    (true, Some(rule)) => json!(format!("{fuzz} --template ID {job} {rule}")),
                    _ => Value::Null,
                },
            }));
        }
        for requirement in &requirements {
            if requirement["covered"] == true {
                continue;
            }
            let truth = requirement["truth"].as_str().unwrap_or_default();
            // The valuation that reaches the requirement's node with its truth: the nodes before
            // it with the truths that reach it, then the node.
            let valuation = |truth: &str| {
                let mut valuation = requirement["reaching"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .map(|step| {
                        format!(
                            "{} {}",
                            step["text"].as_str().unwrap_or_default(),
                            step["truth"]
                        )
                    })
                    .collect::<Vec<_>>();
                valuation.push(format!(
                    "{} {truth}",
                    requirement["text"].as_str().unwrap_or_default()
                ));
                listed(&valuation)
            };
            let outcome = |words: &str| match requirement["node_truth"].as_str() {
                Some(node_truth) => format!(
                    "a case that enters {name} with its condition {words} ({})",
                    valuation(node_truth)
                ),
                None => format!("a case that enters {name} with its condition {words}"),
            };
            let text = match truth {
                "held" => outcome("holding"),
                "refuted" => outcome("false"),
                _ => format!("a case that enters {name} with {}", valuation(truth)),
            };
            let touched = ids(&requirement["touched_only_by"]);
            requirement_targets.push(json!({
                "family": "requirements",
                "item": requirement["id"],
                "text": format!("{text}{}", touched_note(&touched)),
                "file": file,
                "line": line,
                "programs": entered,
                "pattern": null,
                "fuzz": null,
            }));
        }
        requirement_items.extend(requirements);
    }
    let obligations = status_counts.get(FIRED).copied().unwrap_or(0)
        + status_counts.get(MATCHED).copied().unwrap_or(0)
        + status_counts.get(UNMATCHED).copied().unwrap_or(0);
    let fired = status_counts.get(FIRED).copied().unwrap_or(0);
    let count = |status: &str| status_counts.get(status).copied().unwrap_or(0);
    let requirement_covered = requirement_items
        .iter()
        .filter(|item| item["covered"] == true)
        .count();
    let requirement_obligations = requirement_items.len();
    let rules = &mut document["families"]["rules"];
    rules["obligations"] = json!(obligations);
    rules["covered"] = json!(fired);
    rules["measure"] = measure(fired, obligations);
    rules["counts"] = json!({
        "fired": count(FIRED),
        "matched": count(MATCHED),
        "unmatched": count(UNMATCHED),
        "out_of_scope": count(OUT_OF_SCOPE),
        "claim_helper": count(CLAIM_HELPER),
        "no_coverage_signal": count(NO_COVERAGE_SIGNAL),
    });
    let families = &mut document["families"];
    families["requirements"] = json!({
        "tier": 1,
        "obligations": requirement_obligations,
        "covered": requirement_covered,
        "measure": measure(requirement_covered, requirement_obligations),
        "counts": {
            "covered": requirement_covered,
            "open": requirement_obligations - requirement_covered,
        },
        "items": requirement_items,
    });
    families["syntax"] = Value::Null;
    families["rule_windows"] = Value::Null;
    families["syntax_paths"] = Value::Null;
    families["flips"] = json!({
        "tier": 2,
        "run": false,
        "obligations": null,
        "reason": FLIPS_NOT_BUILT,
        "items": [],
    });
    targets.extend(requirement_targets);
    let per_family = |covered: usize, obligations: usize| {
        json!({
            "obligations": obligations,
            "covered": covered,
            "argued": 0,
            "open": obligations - covered,
        })
    };
    let mut summary = summary_programs;
    summary["open"] = json!(targets.len());
    summary["argued"] = json!(0);
    summary["per_family"] = json!({
        "rules": per_family(fired, obligations),
        "requirements": per_family(requirement_covered, requirement_obligations),
    });
    document["targets"] = Value::Array(targets);
    document["summary"] = summary;
}

/// A measure as text: a percentage with one decimal, `-` without obligations.
fn percent(measure: &Value) -> String {
    measure
        .as_f64()
        .map_or_else(|| "-".to_owned(), |ratio| format!("{:.1}%", ratio * 100.0))
}

/// The `--output text` rendering of a coverage document: one line per family with covered /
/// obligations and the measure, the programs that cannot count, then one line per open target
/// with its position, its pattern and its fuzz hint. It is a reading aid, not a lock: its
/// wording may change without any coverage changing (`--output verdicts` is the lock format). The error names what
/// the document is when it is no coverage document.
pub fn text(document: &Value) -> Result<String, String> {
    if document["schema"] != COVERAGE_SCHEMA {
        return Err(format!(
            "--output text renders a coverage document, not {}",
            document["schema"]
                .as_str()
                .unwrap_or("a document with no schema")
        ));
    }
    let mut out = String::new();
    if document["spec"]["outcome"] == "refused" {
        out.push_str(&format!(
            "coverage: the specification is refused at stage {}, {}: {}\n",
            document["spec"]["stage"].as_str().unwrap_or("?"),
            document["spec"]["reason"].as_str().unwrap_or("?"),
            document["spec"]["detail"].as_str().unwrap_or("no detail"),
        ));
        return Ok(out);
    }
    let summary = &document["summary"];
    out.push_str(&format!(
        "coverage: {} open, {} argued; {} programs, {} comparable\n",
        summary["open"], summary["argued"], summary["programs"], summary["comparable"]
    ));
    let families = &document["families"];
    for family in ["rules", "requirements"] {
        let value = &families[family];
        let what = if family == "rules" {
            "fired"
        } else {
            "covered"
        };
        out.push_str(&format!(
            "{family}: {} of {} {what} ({})",
            value["covered"],
            value["obligations"],
            percent(&value["measure"])
        ));
        if family == "rules" {
            let counts = &value["counts"];
            out.push_str(&format!(
                "; {} matched, {} unmatched; not obligations: {} out of scope, {} claim helper, \
                 {} no coverage signal",
                counts["matched"],
                counts["unmatched"],
                counts["out_of_scope"],
                counts["claim_helper"],
                counts["no_coverage_signal"]
            ));
        }
        out.push('\n');
    }
    for family in ["syntax", "rule_windows", "syntax_paths"] {
        if families[family].is_null() {
            out.push_str(&format!("{family}: not built\n"));
        }
    }
    if families["flips"]["run"] == false {
        out.push_str(&format!(
            "flips: not run: {}\n",
            families["flips"]["reason"].as_str().unwrap_or_default()
        ));
    }
    for program in document["programs"].as_array().into_iter().flatten() {
        if program["class"] != "comparable" {
            out.push_str(&format!(
                "program {}: {}, counts for nothing: {}\n",
                program["id"].as_str().unwrap_or("?"),
                program["class"].as_str().unwrap_or("?"),
                program["cause"].as_str().unwrap_or("no cause"),
            ));
        }
    }
    let targets = document["targets"]
        .as_array()
        .map_or(&[][..], Vec::as_slice);
    if !targets.is_empty() {
        out.push_str("targets:\n");
    }
    for target in targets {
        let at = match (target["file"].as_str(), target["line"].as_u64()) {
            (Some(file), Some(line)) => format!(" ({file}:{line})"),
            _ => String::new(),
        };
        out.push_str(&format!(
            "  {}{at}: {}\n",
            target["item"].as_str().unwrap_or("?"),
            target["text"].as_str().unwrap_or_default()
        ));
        if let Some(pattern) = target["pattern"].as_str() {
            out.push_str(&format!("    pattern: {pattern}\n"));
        }
        if let Some(fuzz) = target["fuzz"].as_str() {
            out.push_str(&format!("    fuzz: {fuzz}\n"));
        }
    }
    Ok(out)
}

/// The open ids of each family of a coverage document, in item order: what its verdicts
/// rendering lists ([`crate::verdicts`]).
#[must_use]
pub fn open_ids(document: &Value) -> Vec<(&'static str, Vec<String>)> {
    ["rules", "requirements"]
        .into_iter()
        .map(|family| {
            let open = document["families"][family]["items"]
                .as_array()
                .into_iter()
                .flatten()
                .filter(|item| item["covered"] == false)
                .filter_map(|item| item["id"].as_str().map(str::to_owned))
                .collect();
            (family, open)
        })
        .collect()
}

/// The object a rule item names its sentence by, for readers that look one up by position.
#[must_use]
pub fn rule_item<'d>(document: &'d Value, at: &SentenceRef) -> Option<&'d Map<String, Value>> {
    document["families"]["rules"]["items"]
        .as_array()?
        .iter()
        .filter_map(Value::as_object)
        .find(|item| {
            item.get("module").and_then(Value::as_str) == Some(at.module.as_str())
                && item.get("index").and_then(Value::as_u64) == Some(u64::from(at.index))
        })
}
