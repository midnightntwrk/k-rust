//! K7's drivers: for each slot of the term families, the program that applies a case's sentence
//! to its construct, and the cells the run must end with ([`super::super::k7`]).
//!
//! Each driver writes its program in the terms base's program grammar: the case's command
//! applied to the witness of a matched construct (`Cmd::NAME(x, HOLE)` takes `cNAME(1, w)`), or
//! to values that let a built construct be read (`cNAME(1, 0)`). A matched position that is not
//! the computation cell's (a map's key or value, a list's element, a collection's instance) is
//! set up first by the base's driver commands, one rewrite step each, joined by `then`; a
//! function the equation forms define is applied from a rule (`call`, `sizeof`); a desugar's or
//! an alias's subject is written in the program, which `krs run`'s parse expands; an initializer
//! is read before any step.
//!
//! The run is bounded by the steps the driver counts, so a sentence that applies again to what
//! it wrote (`_ => Cmd::Go()` at a root, a local rule's `x => Cmd::Go()`) is observed after its
//! application. Each case's command is its own, so only its sentence can take its program; the
//! sentences that hold no command of their own (a subject's root) are run apart
//! ([`super::super::Case::unkeyed`]).

use std::cell::Cell;

use super::super::Command;
use super::super::k7::{Ground, K7, Meaning, Run, SkipKind, Status};
use super::{Side, Slot, Spelling, go, hold, int, pair};

/// The term a driver puts at its hole, and what it checks of it.
struct Hole {
    term: Ground,
    status: Status,
}

type Read = Result<Hole, K7>;

/// What a slot's driver reads of its case. In counter mode the hole's witness is the spelling's
/// counter-witness, a term it must not match.
struct Driver<'a> {
    slot: &'a Slot,
    spelling: &'a Spelling,
    command: &'a Command,
    counter: bool,
    /// Whether the plan read the hole's witness, the only reading a counter-witness replaces.
    read_witness: Cell<bool>,
}

/// Why a form has no driver, if it has none.
fn undriven(slot: &Slot) -> Option<&'static str> {
    Some(match slot.form {
        "claim" | "cells-claim" => {
            "a claim is proved, not run, and needs a prover (L4 keeps claims in the fixture gates)"
        }
        "simplification" => {
            "a simplification only rewrites what a prover simplifies, and needs a prover"
        }
        "context-alias" => {
            "a context alias acts only through a production strict in it, and neither the base nor the case declares one"
        }
        "shorthand" => {
            "the function is internal: it has no program syntax, and no base sentence can name the case's function"
        }
        "constant" => {
            "a constant has no program syntax, and no base sentence can name the case's constant"
        }
        _ => return None,
    })
}

/// K7's plan for `spelling` at `slot`, whose case's command is `command`.
pub(super) fn plan(slot: &Slot, spelling: &Spelling, command: &Command) -> K7 {
    if let Some(reason) = undriven(slot) {
        return K7::skip(SkipKind::Form, reason);
    }
    Driver::new(slot, spelling, command, false)
        .plan()
        .unwrap_or_else(|skip| skip)
}

/// K7's counter plan for `spelling` at `slot`: the case's program on the spelling's
/// counter-witness, where its plan reads the witness, which must not apply the case's sentence.
/// The run takes one step fewer than the sentence's plan (it stops before the sentence), and an
/// equation's call leaves `Probe` unevaluated. None for a static clause, whose production a program
/// that does not match its subject is left unexpanded, an error rather than an observation.
pub(super) fn counter_plan(slot: &Slot, spelling: &Spelling, command: &Command) -> Option<Run> {
    if undriven(slot).is_some() || matches!(slot.form, "desugar" | "alias") {
        return None;
    }
    let driver = Driver::new(slot, spelling, command, true);
    let K7::Run(mut run) = driver.plan().ok()? else {
        return None;
    };
    if !driver.read_witness.get() {
        return None;
    }
    if matches!(slot.form, "equation" | "table") {
        return Some(run);
    }
    run.steps = run.steps.checked_sub(1)?;
    run.cells = Vec::new();
    run.status = Status::Liveness;
    Some(run)
}

impl<'a> Driver<'a> {
    fn new(slot: &'a Slot, spelling: &'a Spelling, command: &'a Command, counter: bool) -> Self {
        Self {
            slot,
            spelling,
            command,
            counter,
            read_witness: Cell::new(false),
        }
    }
}

impl Driver<'_> {
    /// The case's command applied to `fields`.
    fn command(&self, fields: Vec<Ground>) -> Ground {
        Ground::ctor(&format!("Cmd::{}", self.command.name), fields)
    }

    /// The spelling's own witness, or in counter mode its counter-witness.
    fn own_witness(&self) -> Result<Ground, K7> {
        self.read_witness.set(true);
        let (witness, kind) = if self.counter {
            (&self.spelling.counter, SkipKind::Witness)
        } else {
            (&self.spelling.witness, SkipKind::Witness)
        };
        witness.clone().map_err(|reason| K7::skip(kind, reason))
    }

    /// A set's element where a pattern reads it, which reads as a key does (decision D2): the
    /// spelling's value, looked up, where it denotes one, and its witness otherwise.
    fn element(&self) -> Read {
        if !self.counter
            && let Meaning::Value(value) = &self.spelling.value
            && *value != Ground::Any
        {
            return Ok(Hole {
                term: value.clone(),
                status: Status::Value,
            });
        }
        Ok(Hole {
            term: self.own_witness()?,
            status: Status::Liveness,
        })
    }

    /// The witness of the hole, where a pattern reads it: the spelling's, inside what the opener
    /// writes around it.
    fn witness(&self) -> Read {
        if self.slot.opener == Some("set-element") {
            let element = self.element()?;
            return Ok(Hole {
                term: Ground::set(vec![element.term]),
                status: element.status,
            });
        }
        let witness = self.own_witness()?;
        let term = match self.slot.opener {
            // A counter-witness `Cmd::Go()` would match the other alternative.
            Some("or-branch") if self.counter && witness == go() => {
                return Err(K7::skip(
                    SkipKind::Witness,
                    "the counter-witness is the other alternative, Cmd::Go()",
                ));
            }
            None | Some("as-body" | "or-branch" | "rewrite-left") => witness,
            // `z`, a name nothing else binds, is any term: 0.
            Some("beside-fresh") => pair(witness, int(0)),
            Some("set-element-beside-fresh") => Ground::set(vec![pair(witness, int(0))]),
            Some("set-concat") => Ground::set(vec![int(1), witness]),
            Some(opener) => {
                return Err(K7::skip(
                    SkipKind::Form,
                    format!("the {opener} opener reads its hole as a built term"),
                ));
            }
        };
        Ok(Hole {
            term,
            status: Status::Liveness,
        })
    }

    /// What the hole denotes where it is built: the spelling's meaning, inside what the opener
    /// writes around it.
    fn meaning(&self) -> Result<Meaning, K7> {
        let spelling = &self.spelling.value;
        // `Size(HOLE)` reads the hole inside an application of `Size`, which no equation of the
        // base evaluates, so it stays as written around the hole's value: `Size` is no value
        // here, only a wrapper the run shows the hole's value in.
        let wrapped = |wrap: fn(Ground) -> Ground| match spelling {
            Meaning::Value(value) => Meaning::Value(wrap(value.clone())),
            Meaning::Unstated(_) => Meaning::Value(wrap(Ground::Any)),
            other => other.clone(),
        };
        Ok(match self.slot.opener {
            None | Some("let-body" | "rewrite-right") => spelling.clone(),
            // `{ let HOLE = x; BODY }` is BODY where the pattern matches x = 1, and undefined
            // where it does not.
            Some("let-pattern") if self.spelling.matches_x => {
                Meaning::Value(if self.slot.side == Side::Guard {
                    Ground::Bool(true)
                } else {
                    int(1)
                })
            }
            Some("let-pattern") => Meaning::Undefined("the let's pattern does not match x = 1"),
            Some("matches-pattern") => Meaning::Value(Ground::Bool(self.spelling.matches_x)),
            Some("function-argument") => wrapped(|value| Ground::unevaluated("size", vec![value])),
            // `Cmd::Pair { a: HOLE, ..p }` over the matched `p`, `pair(5, 6)`.
            Some("update-field") => wrapped(|value| pair(value, int(6))),
            Some("closure-body") => {
                Meaning::NoTerm("a matching-logic predicate, which only a prover reads")
            }
            Some(opener) => {
                return Err(K7::skip(
                    SkipKind::Form,
                    format!("the {opener} opener reads its hole as a pattern"),
                ));
            }
        })
    }

    /// What the hole denotes where it is built, and what K7 checks of it.
    fn value(&self) -> Read {
        match self.meaning()? {
            Meaning::Value(term) => Ok(Hole {
                status: if contains_any(&term) {
                    Status::Liveness
                } else {
                    Status::Value
                },
                term,
            }),
            Meaning::Unstated(_) => Ok(Hole {
                term: Ground::Any,
                status: Status::Liveness,
            }),
            Meaning::Undefined(reason) | Meaning::NoTerm(reason) => {
                Err(K7::skip(SkipKind::Value, reason))
            }
        }
    }

    /// A map key in a pattern: computed and looked up, or matched (a selection). A depth-1 key
    /// reads as a set's element does ([`Self::element`]); a key an opener writes is a selection
    /// below `@`, `|` or a name nothing else binds, and computed below a `let`, a `k::matches!`,
    /// a function and a record update.
    fn key(&self) -> Read {
        match self.slot.opener {
            None => self.element(),
            Some("as-body" | "or-branch" | "beside-fresh") => self.witness(),
            Some(_) => self.value(),
        }
    }

    /// The condition's value, a `Bool` the driver predicts the sentence by. A condition with no
    /// value under the binders' values does not hold, so the sentence must not apply.
    fn guard(&self) -> Result<bool, K7> {
        match self.meaning()? {
            Meaning::Value(Ground::Bool(value)) => Ok(value),
            Meaning::Undefined(_) => Ok(false),
            Meaning::Value(other) => Err(K7::skip(
                SkipKind::Value,
                format!("the condition's stated value, {other}, is no Bool"),
            )),
            Meaning::Unstated(reason) | Meaning::NoTerm(reason) => {
                Err(K7::skip(SkipKind::Value, reason))
            }
        }
    }

    /// A run of `program` that applies the case's sentence after `setup` steps of the driver's,
    /// and ends with `cells`.
    fn applied(
        program: &Ground,
        steps: u64,
        cells: Vec<(&str, Ground)>,
        status: Status,
    ) -> Result<K7, K7> {
        if contains_any(program) {
            return Err(K7::skip(
                SkipKind::Witness,
                "the program would hold a value the generator does not state",
            ));
        }
        let program = program.program().ok_or_else(|| {
            K7::skip(
                SkipKind::Witness,
                format!("no program writes {program}, the term the driver needs"),
            )
        })?;
        Ok(K7::Run(Run {
            program,
            variables: Vec::new(),
            depth: steps,
            steps,
            cells: cells
                .into_iter()
                .map(|(cell, term)| (cell.to_owned(), term))
                .collect(),
            status,
        }))
    }

    /// A run whose condition decides it: the sentence applies, in `steps`, ending with `cells`,
    /// where the condition is true, and leaves `program` in place where it is false.
    fn guarded(
        &self,
        program: &Ground,
        steps: u64,
        cells: Vec<(&str, Ground)>,
        unapplied: Vec<(&str, Ground)>,
    ) -> Result<K7, K7> {
        let holds = self.guard()?;
        let mut run = match Self::applied(
            program,
            steps,
            if holds { cells } else { unapplied },
            Status::Value,
        )? {
            K7::Run(run) => run,
            skip @ K7::Skip(_) => return Ok(skip),
        };
        if !holds {
            run.steps -= 1;
        }
        Ok(K7::Run(run))
    }

    /// A run that sets the cells up with `setup`, one step, and then applies the case's sentence
    /// to `command`: `then(setup, command)`, three steps.
    fn set_up(
        setup: Ground,
        command: Ground,
        cells: Vec<(&str, Ground)>,
        status: Status,
    ) -> Result<K7, K7> {
        let program = Ground::ctor("Cmd::Then", vec![setup, command]);
        Self::applied(&program, 3, cells, status)
    }

    /// The plan of the case.
    #[expect(
        clippy::too_many_lines,
        reason = "One match of the closed slot set; each arm is one slot's driver."
    )]
    fn plan(&self) -> Result<K7, K7> {
        let one = || int(1);
        let k = |items: Vec<Ground>| ("k", Ground::Seq(items));
        let fields = |a: Ground, b: Ground| vec![a, b];
        // The case's command over `x` = 1 and a second field the template does not read.
        let reading = || self.command(fields(one(), int(0)));
        let call =
            |argument: Ground| Ground::ctor("Cmd::Call", vec![self.command(Vec::new()), argument]);
        let setup = |command: &str, arguments: Vec<Ground>| {
            Ground::ctor(&format!("Cmd::{command}"), arguments)
        };
        let env =
            |key: Ground, value: Ground| setup("SetEnv", vec![Ground::map(vec![(key, value)])]);
        let position = self.slot.position;
        match (self.slot.form, position) {
            ("rule" | "sort-rule", "subject") => {
                let witness = self.witness()?;
                Self::applied(
                    &self.command(fields(one(), witness.term)),
                    1,
                    vec![k(vec![hold(one())])],
                    witness.status,
                )
            }
            ("rule" | "sort-rule", "subject-depth-2") => {
                let witness = self.witness()?;
                Self::applied(
                    &self.command(fields(one(), hold(witness.term))),
                    1,
                    vec![k(vec![hold(one())])],
                    witness.status,
                )
            }
            // `HOLE => Cmd::Go()` over a whole computation item: the witness is the program
            // where it is a `Stmt`, and goes first in the computation cell otherwise.
            ("rule" | "sort-rule", "subject-root" | "subject-root-term") => {
                let witness = self.witness()?;
                if witness.term.is_statement() {
                    Self::applied(&witness.term, 1, vec![k(vec![go()])], witness.status)
                } else {
                    let program = setup("Then", vec![witness.term, go()]);
                    Self::applied(&program, 2, vec![k(vec![go(), go()])], witness.status)
                }
            }
            ("rule" | "sort-rule", "result") => {
                let value = self.value()?;
                let program = match self.slot.opener {
                    // The update's base `p @ Cmd::Pair { .. }` is the command's second field.
                    Some("update-field") => self.command(fields(one(), pair(int(5), int(6)))),
                    _ => reading(),
                };
                Self::applied(&program, 1, vec![k(vec![hold(value.term)])], value.status)
            }

            ("rule", "guard") => self.guarded(
                &reading(),
                1,
                vec![k(vec![hold(one())])],
                vec![k(vec![reading()])],
            ),
            // `Cmd::NAME(k::rewrite!(x => Cmd::Go()), HOLE)`: the first field becomes `go`, the
            // second is kept, or rewritten by the rewrite the hole holds.
            ("local-rule" | "cells-local", "subject") => {
                let rewrites = self
                    .spelling
                    .nodes
                    .first()
                    .is_some_and(|node| node.construct == super::C::Rewrite);
                let (written, kept) = match self.slot.opener {
                    Some("rewrite-left") => (self.witness()?.term, go()),
                    Some("rewrite-right") => {
                        let value = self.value()?;
                        (int(0), value.term)
                    }
                    _ if rewrites => {
                        let value = self.value()?;
                        (self.witness()?.term, value.term)
                    }
                    _ => {
                        let witness = self.witness()?.term;
                        (witness.clone(), witness)
                    }
                };
                let status = if rewrites || self.slot.opener == Some("rewrite-right") {
                    Status::Value
                } else {
                    Status::Liveness
                };
                let after = self.command(fields(go(), kept));
                Self::applied(
                    &self.command(fields(one(), written)),
                    1,
                    vec![k(vec![after])],
                    status,
                )
            }
            // A single-body rule whose whole subject is the hole: a rewrite's left side matches
            // the program, its right side is written.
            ("local-rule", "subject-root") => {
                let witness = self.witness()?;
                let value = self.value()?;
                Self::applied(&witness.term, 1, vec![k(vec![value.term])], Status::Value)
            }
            ("cells" | "readable", "subject") => {
                let witness = self.witness()?;
                Self::applied(
                    &self.command(fields(one(), witness.term)),
                    1,
                    vec![k(empty_items())],
                    witness.status,
                )
            }
            ("readable", "subject-depth-2") => {
                let witness = self.witness()?;
                Self::applied(
                    &self.command(fields(one(), hold(witness.term))),
                    1,
                    vec![k(empty_items())],
                    witness.status,
                )
            }
            // The hole is the computation item before the command.
            ("cells" | "readable", "item-root") => {
                let witness = self.witness()?;
                let program = setup("Then", vec![witness.term, reading()]);
                Self::applied(&program, 2, vec![k(empty_items())], witness.status)
            }
            ("cells" | "readable", "result") => {
                let value = self.value()?;
                Self::applied(&reading(), 1, vec![k(vec![hold(value.term)])], value.status)
            }
            ("rule" | "sort-rule", "result-root") | ("cells" | "readable", "result-item-root") => {
                let value = self.value()?;
                Self::applied(&reading(), 1, vec![k(vec![value.term])], value.status)
            }
            ("readable", "guard") => self.guarded(
                &reading(),
                1,
                vec![k(empty_items())],
                vec![k(vec![reading()])],
            ),
            ("cells" | "readable", "map-key") => {
                let key = self.key()?;
                let command = match self.slot.opener {
                    Some("update-field") => self.command(fields(one(), pair(int(5), int(6)))),
                    _ => reading(),
                };
                Self::set_up(
                    env(key.term, int(0)),
                    command,
                    vec![k(empty_items())],
                    key.status,
                )
            }
            ("cells" | "readable", "map-value") => {
                let witness = self.witness()?;
                Self::set_up(
                    env(one(), witness.term),
                    reading(),
                    vec![k(empty_items())],
                    witness.status,
                )
            }
            ("cells", "result-map-key") => {
                let value = self.value()?;
                Self::applied(
                    &reading(),
                    1,
                    vec![
                        k(empty_items()),
                        ("env", Ground::map(vec![(value.term, one())])),
                    ],
                    value.status,
                )
            }
            ("cells", "result-map-value") => {
                let value = self.value()?;
                Self::applied(
                    &reading(),
                    1,
                    vec![
                        k(empty_items()),
                        ("env", Ground::map(vec![(one(), value.term)])),
                    ],
                    value.status,
                )
            }
            // `map![x -> 1, (x) -> HOLE, ..rest]` over the matched `x -> v`: one key written
            // twice, under two spellings, the later value the map's.
            ("cells", "result-map-framed") => {
                let value = self.value()?;
                Self::set_up(
                    env(one(), int(0)),
                    reading(),
                    vec![
                        k(empty_items()),
                        ("env", Ground::map(vec![(one(), value.term)])),
                    ],
                    value.status,
                )
            }
            // `map![x -> HOLE, ..m]` over the whole map `m`, `{1 ↦ 0, 2 ↦ 0}`: the entry is written
            // over it.
            ("cells", "result-map-whole") => {
                let value = self.value()?;
                Self::set_up(
                    setup(
                        "SetEnv",
                        vec![Ground::map(vec![(one(), int(0)), (int(2), int(0))])],
                    ),
                    reading(),
                    vec![
                        k(empty_items()),
                        (
                            "env",
                            Ground::map(vec![(one(), value.term), (int(2), int(0))]),
                        ),
                    ],
                    value.status,
                )
            }
            // `map![HOLE -> 1, ..rest]` over the remainder `{2 ↦ 0}` the subject's `x -> v` leaves
            // of `{1 ↦ 0, 2 ↦ 0}`: the entry is written over the remainder.
            ("cells", "result-map-framed-key") => {
                let key = self.value()?;
                Self::set_up(
                    setup(
                        "SetEnv",
                        vec![Ground::map(vec![(one(), int(0)), (int(2), int(0))])],
                    ),
                    reading(),
                    vec![
                        k(empty_items()),
                        (
                            "env",
                            Ground::map(vec![(int(2), int(0)), (key.term, one())]),
                        ),
                    ],
                    key.status,
                )
            }
            ("readable", "list-element") => {
                let witness = self.witness()?;
                let list = setup("SetStack", vec![Ground::List(vec![witness.term])]);
                Self::set_up(list, reading(), vec![k(empty_items())], witness.status)
            }
            ("readable", "cons-element") => {
                let witness = self.witness()?;
                let items = Ground::ctor(
                    "Seq::Cons",
                    vec![witness.term, Ground::ctor("Seq::Nil", Vec::new())],
                );
                Self::set_up(
                    setup("SetSeq", vec![items]),
                    reading(),
                    vec![k(empty_items())],
                    witness.status,
                )
            }
            // A Set collection's instance is the set's element, read as a key is (D2): the
            // instance holding a computed spelling is looked up by its value.
            ("readable", "collection-child" | "set-instance-child") => {
                let (witness, command) = if position == "collection-child" {
                    (self.witness()?, "AddMember")
                } else {
                    (self.element()?, "AddToken")
                };
                Self::set_up(
                    setup(command, vec![hold(witness.term)]),
                    reading(),
                    vec![k(empty_items())],
                    witness.status,
                )
            }
            ("readable", "map-key-child" | "map-value-child") => {
                let witness = self.witness()?;
                let row = if position == "map-key-child" {
                    vec![hold(witness.term), go()]
                } else {
                    vec![go(), hold(witness.term)]
                };
                Self::set_up(
                    setup("AddRow", row),
                    reading(),
                    vec![k(empty_items())],
                    witness.status,
                )
            }
            // `stack: [_, ..]` read and `stack: [HOLE, ..]` written: the stack starts as `[0]`.
            ("readable", "result-list-element") => {
                let value = self.value()?;
                Self::set_up(
                    setup("SetStack", vec![Ground::List(vec![int(0)])]),
                    reading(),
                    vec![k(empty_items()), ("stack", Ground::List(vec![value.term]))],
                    value.status,
                )
            }
            // `#[k::context(hole = h)]` over `Cmd::NAME(h, x, HOLE)`: `h` is the token `word`,
            // which is no `KResult`, so the context heats it to the front of the computation.
            ("context", "subject") => {
                let witness = self.witness()?;
                let program = self.command(vec![word(), one(), witness.term]);
                Self::applied(
                    &program,
                    1,
                    vec![k(vec![word(), Ground::Any])],
                    Status::Liveness,
                )
            }
            ("context", "guard") => {
                let program = self.command(vec![word(), one(), int(0)]);
                self.guarded(
                    &program,
                    1,
                    vec![k(vec![word(), Ground::Any])],
                    vec![k(vec![program.clone()])],
                )
            }
            ("context", "subject-root") => Err(K7::skip(
                SkipKind::Witness,
                "the context's hole is the construct's x, which K7 binds to 1, a KResult no context heats",
            )),
            // `Probe(Cmd::NAME(), ..)`, applied by the base's rule `call(a, b) => hold(probe(a, b))`.
            // `Probe(Cmd::NAME(), HOLE)`: the call's result is 0 where the equation applies; a
            // counter-witness leaves the application of `Probe` as written.
            ("equation" | "table", "subject" | "subject-depth-2") => {
                let witness = self.witness()?;
                let argument = if position == "subject" {
                    witness.term
                } else {
                    hold(witness.term)
                };
                let result = if self.counter {
                    Ground::unevaluated("probe", vec![self.command(Vec::new()), argument.clone()])
                } else {
                    int(0)
                };
                Self::applied(
                    &call(argument),
                    1,
                    vec![k(vec![hold(result)])],
                    witness.status,
                )
            }
            ("equation" | "table", "result") => {
                let value = self.value()?;
                Self::applied(
                    &call(one()),
                    1,
                    vec![k(vec![hold(Ground::unevaluated("size", vec![value.term]))])],
                    value.status,
                )
            }
            ("equation", "guard") => {
                let unapplied = Ground::unevaluated("probe", vec![self.command(Vec::new()), one()]);
                let mut run = self.guarded(
                    &call(one()),
                    1,
                    vec![k(vec![hold(int(0))])],
                    vec![k(vec![hold(unapplied)])],
                )?;
                // The rule applies `Probe` either way: one step.
                if let K7::Run(run) = &mut run {
                    run.steps = 1;
                }
                Ok(run)
            }
            // The equation's subject is the function's application: `Size(x)`, which the base's
            // rule `sizeof(a) => hold(size(a))` applies.
            ("equation", "subject-root") if self.spelling.text == "Size(x)" => Self::applied(
                &setup("SizeOf", vec![one()]),
                1,
                vec![k(vec![hold(int(0))])],
                Status::Liveness,
            ),
            ("equation", "subject-root") => Err(K7::skip(
                SkipKind::Form,
                "the base applies no function but Probe and Size from a rule",
            )),
            // A static clause expands what a program writes as `krs run` parses it: no step.
            ("desugar" | "alias", "subject") => {
                let witness = self.witness()?;
                literal(&witness.term)?;
                Self::expanded(
                    &self.command(fields(one(), witness.term)),
                    vec![k(vec![hold(one())])],
                    witness.status,
                )
            }
            ("desugar" | "alias", "subject-root") => {
                let witness = self.witness()?;
                literal(&witness.term)?;
                Self::expanded(&witness.term, vec![k(vec![go()])], witness.status)
            }
            ("alias", "subject-root-binding") => {
                let witness = self.witness()?;
                literal(&witness.term)?;
                Self::expanded(&witness.term, vec![k(vec![hold(one())])], witness.status)
            }
            ("desugar", "result-root") => {
                let value = self.value()?;
                Self::expanded(&reading(), vec![k(vec![value.term])], value.status)
            }
            ("desugar", "result") => {
                let value = self.value()?;
                Self::expanded(&reading(), vec![k(vec![hold(value.term)])], value.status)
            }
            ("alias", "result-root") => {
                let value = self.value()?;
                Self::expanded(
                    &self.command(vec![one()]),
                    vec![k(vec![value.term])],
                    value.status,
                )
            }
            ("alias", "result-root-ground") => {
                let value = self.value()?;
                Self::expanded(
                    &self.command(Vec::new()),
                    vec![k(vec![value.term])],
                    value.status,
                )
            }
            ("alias", "result") => {
                let value = self.value()?;
                Self::expanded(
                    &self.command(vec![one()]),
                    vec![k(vec![pair(one(), value.term)])],
                    value.status,
                )
            }
            // The initial configuration, before any step: the program `go`, then the item.
            ("init", "item" | "item-root" | "item-depth-2" | "variable-item") => {
                let value = self.value()?;
                let item = match position {
                    "item-root" => value.term,
                    "item-depth-2" => hold(hold(value.term)),
                    _ => hold(value.term),
                };
                let mut items = vec![go()];
                if position == "variable-item" {
                    items.push(one());
                }
                items.push(item);
                let mut run = Self::expanded(&go(), vec![k(items)], value.status)?;
                if let (K7::Run(run), "variable-item") = (&mut run, position) {
                    run.variables.push(("x".to_owned(), "1".to_owned()));
                }
                Ok(run)
            }
            (form, position) => Err(K7::skip(
                SkipKind::Form,
                format!("no driver is written for {form}/{position}"),
            )),
        }
    }

    /// A run of `program` that takes no step: the case's clause acts as the program is read, or
    /// its initializer as the configuration is built.
    fn expanded(program: &Ground, cells: Vec<(&str, Ground)>, status: Status) -> Result<K7, K7> {
        Self::applied(program, 0, cells, status)
    }
}

/// Whether a program writes `term` without a maker, as a static clause's subject must meet it:
/// the clause rewrites the program as written, before any function is evaluated.
fn literal(term: &Ground) -> Result<(), K7> {
    term.literal_program().map(drop).ok_or_else(|| {
        K7::skip(
            SkipKind::Witness,
            format!(
                "a program writes {term} only through a maker, a function, which a static clause's expansion of the program meets unevaluated"
            ),
        )
    })
}

/// The computation cell's content after a rule that consumes its command: nothing.
const fn empty_items() -> Vec<Ground> {
    Vec::new()
}

/// The token `word` of the base's token sort `Word`, which is no `KResult`.
fn word() -> Ground {
    Ground::token("Word", "word")
}

/// Whether `term` holds [`Ground::Any`].
fn contains_any(term: &Ground) -> bool {
    match term {
        Ground::Any => true,
        Ground::Ctor { fields: terms, .. }
        | Ground::Unevaluated {
            arguments: terms, ..
        }
        | Ground::List(terms)
        | Ground::Set(terms)
        | Ground::Seq(terms) => terms.iter().any(contains_any),
        Ground::Map(entries) => entries
            .iter()
            .any(|(key, value)| contains_any(key) || contains_any(value)),
        _ => false,
    }
}
