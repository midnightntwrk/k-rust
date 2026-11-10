//! Explanations of a failed pattern answer (FB50-EXPLAIN; [`super`], "Explanations").
//!
//! An explanation is defined as the answers of patterns derived from the explained one, each
//! asked by the query's own machinery: the route, the matcher, the judge and the cache of every
//! pattern, under the derived pattern's own digest and key ([`super::answer_key`],
//! [`super::chain_answer_key`]). A derived pattern leaves one part of the pattern out
//! ([`crate::pattern::explain`]), so it matches every state the pattern matches: where the pattern
//! is refuted and the derived one hits, the part left out is one no reached state satisfies
//! together with the rest.

use super::{Asked, Context, Lowered, ask_facts};
use crate::pattern::{
    LoweredChain, LoweredPattern, Searcher,
    explain::{CellTable, Parts, vacuous},
    parsed_witness_text, rendered_bindings,
};
use k_rust::kore::{ast::Pattern, parser::parse_pattern};
use kink_patch::Sha256Digest;
use serde_json::{Map, Value, json};
use std::collections::{BTreeMap, BTreeSet};

/// Why a vacuous part is not asked.
pub const VACUOUS: &str = "leaving this part out leaves no constraint: every cell's content is \
     a distinct variable and there is no condition, so every configuration matches; it is not \
     asked and names nothing";

/// What one command's explanations ask through: the query's own means of asking, the
/// configuration's cells, and every derived answer the command already has, by (digest, corpus
/// index), so a pair is asked at most once per command.
pub(super) struct Asker<'q, 'i> {
    pub context: &'q Context<'q>,
    pub inputs: &'q mut crate::admit::InputSession<'i>,
    pub spec: &'q crate::admit::AdmittedSpec,
    pub searcher: &'q mut Searcher,
    pub mismatches: &'q mut Vec<Value>,
    pub cells: &'q CellTable,
    pub answers: &'q mut BTreeMap<(Sha256Digest, usize), Value>,
    /// `{asked, from_cache, records_written}`: the pairs asked, of them answered from the cache,
    /// and the records written.
    pub accounting: &'q mut Value,
}

/// The answer of a derived pattern over a list of programs: the first that hits, in the list's
/// order, else `no` when every program answered a final `no`, else the first program's answer
/// that is neither.
struct Over {
    answer: String,
    program: Option<usize>,
    row: Option<Value>,
    cause: Value,
    cached: bool,
}

/// What a part's witness shows of the part: the cell it left out, or the variables of the
/// conjunct it dropped.
enum Shown<'a> {
    Cell(&'a str),
    Variables(&'a [String]),
    Nothing,
}

impl Asker<'_, '_> {
    /// The row of `asked` on the program at corpus index `index`, its witness as facts: this
    /// command's when it asked the pair before, else asked as every pattern is. A `--verify`
    /// mismatch it finds names the pattern `pattern` and the part `part` (`explain`).
    fn ask(&mut self, pattern: &str, part: &str, index: usize, asked: Asked<'_>) -> Value {
        let key = (asked.digest(), index);
        if let Some(row) = self.answers.get(&key) {
            return row.clone();
        }
        let route = match asked {
            Asked::Pattern(_) => self.context.route,
            Asked::Chain(_) => crate::pattern::Route::ChainRun,
        };
        let mut row = Map::new();
        row.insert("pattern".into(), json!(pattern));
        row.insert(
            "program".into(),
            json!(self.context.manifest.programs[index].id),
        );
        row.insert("claimed".into(), json!(false));
        row.insert("route".into(), json!(route.name()));
        let before = self.mismatches.len();
        let (row, _) = ask_facts(
            self.context,
            self.inputs,
            self.spec,
            self.searcher,
            index,
            &format!("{pattern} (explain: {part})"),
            asked,
            row,
            false,
            self.mismatches,
            self.accounting,
        );
        for mismatch in &mut self.mismatches[before..] {
            mismatch["pattern"] = json!(pattern);
            mismatch["explain"] = json!(part);
        }
        self.accounting["asked"] = json!(self.accounting["asked"].as_u64().unwrap_or(0) + 1);
        self.answers.insert(key, row.clone());
        row
    }

    /// The answer of `asked` over `programs` ([`Over`]), asking them in order up to the first
    /// hit.
    fn over(&mut self, pattern: &str, part: &str, programs: &[usize], asked: Asked<'_>) -> Over {
        let mut open = None;
        let mut cached = true;
        for &index in programs {
            let row = self.ask(pattern, part, index, asked);
            cached &= row["cached"] == true;
            if row["answer"] == "hit" {
                return Over {
                    answer: "hit".into(),
                    program: Some(index),
                    row: Some(row),
                    cause: Value::Null,
                    cached,
                };
            }
            if row["answer"] != "no" && open.is_none() {
                open = Some((index, row));
            }
        }
        match open {
            None => Over {
                answer: "no".into(),
                program: None,
                row: None,
                cause: Value::Null,
                cached,
            },
            Some((index, row)) => Over {
                answer: row["answer"].as_str().unwrap_or("error").to_owned(),
                program: Some(index),
                cause: row["cause"].clone(),
                row: None,
                cached,
            },
        }
    }

    /// The explanation of `lowered`, the pattern `pattern`, on `programs`: one program for a
    /// refuted claim, the corpus in order for an open obligation ([`super`], "Explanations").
    pub(super) fn explain(
        &mut self,
        pattern: &str,
        lowered: &Lowered,
        programs: &[usize],
    ) -> Value {
        let explanation = match lowered {
            Lowered::Pattern(single) => {
                let parts = self.parts(
                    pattern,
                    "",
                    single,
                    &BTreeSet::new(),
                    programs,
                    &|variant| Ok(Lowered::Pattern(variant)),
                );
                json!({"form": "pattern", "parts": parts})
            }
            Lowered::Chain(chain) => self.explain_chain(pattern, chain, programs),
        };
        with_leads(explanation)
    }

    /// A chain's explanation: the longest prefix some program in `programs` completes, each
    /// prefix asked as a chain (one step as a single pattern), and the parts of the step after
    /// it, each asked as the prefix followed by that step without the part.
    fn explain_chain(&mut self, pattern: &str, chain: &LoweredChain, programs: &[usize]) -> Value {
        let steps = chain.steps.len();
        let mut prefix = json!({
            "steps": 0, "of": steps, "program": null, "depth": null, "cached": null,
            "undecided": null,
        });
        let mut matched = 0;
        // The chain itself is refuted, so only its proper prefixes are asked.
        for count in 1..steps {
            let label = format!("steps 1 to {count}");
            let lowered = if count == 1 {
                Ok(Lowered::Pattern(chain.steps[0].pattern.clone()))
            } else {
                LoweredChain::from_parts(chain.parts(count)).map(Lowered::Chain)
            };
            let over = match &lowered {
                Ok(lowered) => self.over(pattern, &label, programs, lowered.asked()),
                Err(detail) => Over {
                    answer: crate::pattern::INVALID_PATTERN.into(),
                    program: None,
                    row: None,
                    cause: json!(detail),
                    cached: false,
                },
            };
            match over.answer.as_str() {
                "hit" => {
                    matched = count;
                    prefix["steps"] = json!(count);
                    prefix["program"] = self.program_id(over.program);
                    prefix["depth"] = over
                        .row
                        .as_ref()
                        .map_or(Value::Null, |row| row["witness"]["depth"].clone());
                    prefix["cached"] = json!(over.cached);
                }
                "no" => break,
                _ => {
                    prefix["undecided"] = json!({
                        "step": count,
                        "answer": over.answer,
                        "program": self.program_id(over.program),
                        "cause": over.cause,
                    });
                    return json!({"form": "chain", "prefix": prefix, "step": null, "parts": []});
                }
            }
        }
        let step = &chain.steps[matched];
        let number = matched + 1;
        let carried = step
            .imports
            .iter()
            .map(|variable| variable.name.clone())
            .collect::<BTreeSet<_>>();
        let before = chain.parts(matched);
        let unless = step.unless.as_ref().map(|unless| unless.pattern.clone());
        let wrap = |variant: LoweredPattern, unless: Option<LoweredPattern>| {
            if matched == 0 {
                Ok(Lowered::Pattern(variant))
            } else {
                let mut parts = before.clone();
                parts.push((variant, unless));
                LoweredChain::from_parts(parts).map(Lowered::Chain)
            }
        };
        let mut parts = self.parts(
            pattern,
            &format!("step {number}: "),
            &step.pattern,
            &carried,
            programs,
            &|variant| wrap(variant, unless.clone()),
        );
        if unless.is_some() {
            let base = part(&format!("step {number}'s unless"), "unless");
            parts.push(match wrap(step.pattern.clone(), None) {
                Ok(lowered) => self.asked_part(pattern, base, &lowered, programs, &Shown::Nothing),
                Err(detail) => refused(base, &detail),
            });
        }
        json!({"form": "chain", "prefix": prefix, "step": number, "parts": parts})
    }

    /// The parts of `lowered` (a single pattern, or a chain's step: `carried` holds the variables
    /// earlier steps carry into it), each left out in turn and asked over `programs` as `wrap`
    /// makes the derived pattern a query (itself, or a chain ending in it). Each label starts with
    /// `prefix`.
    fn parts(
        &mut self,
        pattern: &str,
        prefix: &str,
        lowered: &LoweredPattern,
        carried: &BTreeSet<String>,
        programs: &[usize],
        wrap: &dyn Fn(LoweredPattern) -> Result<Lowered, String>,
    ) -> Vec<Value> {
        let parts = Parts::of(lowered, self.cells, carried);
        // Each conjunct that is a part, by its index in `parts.conjuncts`: its label, numbered
        // from 1 among the parts, and its printed text.
        let conjuncts = parts
            .conjuncts
            .iter()
            .enumerate()
            .filter(|(_, conjunct)| !conjunct.tautology)
            .enumerate()
            .map(|(number, (index, conjunct))| {
                let printed = self.context.reader.print(&conjunct.term, usize::MAX);
                let text = printed["text"].as_str().unwrap_or_default().to_owned();
                (
                    index,
                    (
                        format!("{prefix}requires conjunct {}: {text}", number + 1),
                        printed,
                    ),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let mut out = Vec::new();
        for (index, cell) in parts.cells.iter().enumerate() {
            let mut base = part(&format!("{prefix}cell {}", cell.label), "cell");
            base["cell"] = json!(cell.label);
            base["dropped_conjuncts"] = json!(
                cell.dependent
                    .iter()
                    .filter_map(|at| conjuncts.get(at).map(|(label, _)| label.clone()))
                    .collect::<Vec<_>>()
            );
            let dropped = cell.dependent.iter().copied().collect();
            let variant = parts.without(lowered, Some(index), &dropped, self.searcher.definition());
            out.push(self.variant_part(
                pattern,
                base,
                variant,
                programs,
                wrap,
                &Shown::Cell(&cell.symbol),
            ));
        }
        for (index, (label, printed)) in &conjuncts {
            let conjunct = &parts.conjuncts[*index];
            let mut base = part(label, "conjunct");
            base["conjunct"] = printed.clone();
            let variant = parts.without(
                lowered,
                None,
                &BTreeSet::from([*index]),
                self.searcher.definition(),
            );
            out.push(self.variant_part(
                pattern,
                base,
                variant,
                programs,
                wrap,
                &Shown::Variables(&conjunct.variables),
            ));
        }
        out
    }

    /// The part `base` answered by its derived pattern `variant` over `programs`: refused when
    /// the pattern is, `vacuous` without asking when it matches every configuration, else asked.
    fn variant_part(
        &mut self,
        pattern: &str,
        base: Value,
        variant: Result<LoweredPattern, String>,
        programs: &[usize],
        wrap: &dyn Fn(LoweredPattern) -> Result<Lowered, String>,
        shown: &Shown<'_>,
    ) -> Value {
        let variant = match variant {
            Ok(variant) => variant,
            Err(detail) => return refused(base, &detail),
        };
        if vacuous(&variant, self.cells) {
            let mut base = base;
            base["outcome"] = json!("vacuous");
            base["cause"] = json!(VACUOUS);
            return base;
        }
        match wrap(variant) {
            Ok(lowered) => self.asked_part(pattern, base, &lowered, programs, shown),
            Err(detail) => refused(base, &detail),
        }
    }

    /// The part `base` with the answer of `lowered` over `programs`, and on a hit what the
    /// witness shows of the part (`shown`).
    fn asked_part(
        &mut self,
        pattern: &str,
        mut base: Value,
        lowered: &Lowered,
        programs: &[usize],
        shown: &Shown<'_>,
    ) -> Value {
        let label = base["part"].as_str().unwrap_or_default().to_owned();
        let over = self.over(pattern, &label, programs, lowered.asked());
        base["digest"] = json!(lowered.asked().digest().to_string());
        base["outcome"] = json!(over.answer);
        base["cause"] = over.cause;
        base["program"] = self.program_id(over.program);
        base["cached"] = json!(over.cached);
        if let Some(row) = &over.row {
            base["witness"] = self.shown(&row["witness"], shown);
        }
        base
    }

    /// What a hit's witness `facts` shows of a part: `{depth, state, bindings, rendering}`, the
    /// state's cells only the left-out cell, printed in full as a witness prints a cell its
    /// pattern names, and the bindings only those of the dropped conjunct's variables.
    fn shown(&self, facts: &Value, shown: &Shown<'_>) -> Value {
        let reader = self.context.reader;
        let cells = match shown {
            Shown::Cell(symbol) => parsed_witness_text(&facts["state"]).map_or_else(
                |unreadable| vec![json!({"unreadable": unreadable})],
                |state| {
                    let named = BTreeSet::from([(*symbol).to_owned()]);
                    reader.witness_state(&state, &named)["cells"]
                        .as_array()
                        .into_iter()
                        .flatten()
                        .filter(|cell| cell["named"] == true)
                        .cloned()
                        .collect()
                },
            ),
            Shown::Variables(_) | Shown::Nothing => Vec::new(),
        };
        let bindings = match (shown, &facts["bindings"]) {
            (Shown::Variables(names), Value::Array(bindings)) => rendered_bindings(
                &Value::Array(
                    bindings
                        .iter()
                        .filter(|binding| {
                            binding["variable"]
                                .as_str()
                                .and_then(|text| parse_pattern(text).ok())
                                .is_some_and(|variable| {
                                    matches!(&variable, Pattern::Variable(variable)
                                        if names.contains(&variable.name))
                                })
                        })
                        .cloned()
                        .collect(),
                ),
                reader,
            ),
            (Shown::Variables(_), absent) => rendered_bindings(absent, reader),
            _ => json!([]),
        };
        json!({
            "depth": facts["depth"],
            "state": {"cells": cells},
            "bindings": bindings,
            "rendering": "k",
        })
    }

    fn program_id(&self, index: Option<usize>) -> Value {
        index.map_or(Value::Null, |index| {
            json!(self.context.manifest.programs[index].id)
        })
    }
}

/// A part's entry before it is answered: `{part, kind, cell, conjunct, dropped_conjuncts, digest,
/// outcome, cause, program, cached, witness}`.
fn part(label: &str, kind: &str) -> Value {
    json!({
        "part": label,
        "kind": kind,
        "cell": null,
        "conjunct": null,
        "dropped_conjuncts": [],
        "digest": null,
        "outcome": null,
        "cause": null,
        "program": null,
        "cached": null,
        "witness": null,
    })
}

/// `base` refused: its derived pattern is no pattern the search admits, or no chain.
fn refused(mut base: Value, detail: &str) -> Value {
    base["outcome"] = json!(crate::pattern::INVALID_PATTERN);
    base["cause"] = json!(detail);
    base
}

/// `explanation` with `leads`, the labels of its parts that hit, in order.
fn with_leads(mut explanation: Value) -> Value {
    let leads = explanation["parts"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|part| part["outcome"] == "hit")
        .map(|part| part["part"].clone())
        .collect::<Vec<_>>();
    explanation["leads"] = json!(leads);
    explanation
}
