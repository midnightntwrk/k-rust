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
//! The collection the hole stands in holds an item more than the slot writes where the slot leaves
//! it open (a map read's `..`, a list's, a collection's other instances), and a counter run puts an
//! item more in it where the slot reads it exactly (a set's singleton), as the spellings' own
//! witnesses and counter-witnesses do for an open or exact collection; so a lowering that reads an
//! open collection as exact, or an exact one as open, does not run as stated.
//!
//! The run is bounded by the steps the driver counts, so a sentence that applies again to what
//! it wrote (`_ => Cmd::Go()` at a root, a local rule's `x => Cmd::Go()`) is observed after its
//! application. Each case's command is its own, so only its sentence can take its program; the
//! sentences that hold no command of their own (a subject's root) are run apart
//! ([`super::super::Case::unkeyed`]).

use std::cell::Cell;

use super::super::Command;
use super::super::k7::{Ground, K7, Meaning, Run, SkipKind, Status};
use super::super::positions::Construct;
use super::{Side, Slot, Spelling, go, hold, int, pair};

/// The term a driver puts at its hole, and what it checks of it.
struct Hole {
    term: Ground,
    status: Status,
}

type Read = Result<Hole, K7>;

/// A value no spelling's witness or value is, which the drivers put beside the hole's in the
/// collection the hole stands in: an open collection's witness holds an item more than its
/// pattern writes, and an exact one's counter-witness does.
const EXTRA: i64 = 99;

/// What a slot's driver reads of its case. In counter mode the hole's witness is one of the
/// spelling's counter-witnesses, a term it must not match; in extra mode the exact collection the
/// hole stands in holds an item more than the hole's witness.
struct Driver<'a> {
    slot: &'a Slot,
    spelling: &'a Spelling,
    command: &'a Command,
    counter: Option<Ground>,
    extra: bool,
    /// In an x-counter run ([`Spelling::x_counter`]), `x`'s value, which is also the counter.
    x: Option<Ground>,
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
    Driver::new(slot, spelling, command, None, false)
        .plan()
        .unwrap_or_else(|skip| skip)
}

/// K7's counter plans for `spelling` at `slot`: the case's program on each of the spelling's
/// counter-witnesses, where its plan reads the witness, and, where the hole stands in an exact
/// collection (a set's singleton), on the hole's witness beside an item more, each of which must
/// not apply the case's sentence. A run takes one step fewer than the sentence's plan (it stops
/// before the sentence), and an equation's call leaves `Probe` unevaluated. A static clause's
/// counter run is a program its subject does not match, whose expansion therefore leaves the
/// case's production unexpanded ([`Status::Unexpanded`]); and a program writing a token subject's
/// value in another spelling ([`second_spellings`]) is the same term, which the clause must expand
/// too (finding NT-14-2: static expansion matched a token by its text), while a spelling of a
/// neighbouring value ([`neighbour_values`]: another float format, the other zero) is not.
pub(super) fn counter_plans(slot: &Slot, spelling: &Spelling, command: &Command) -> Vec<Run> {
    if matches!(
        (slot.form, slot.position, slot.opener),
        ("desugar" | "alias", "subject", None)
    ) {
        return static_counter_plans(slot, spelling, command);
    }
    if (slot.form, slot.position, slot.opener) == ("desugar", "subject-beside", None) {
        return beside_plans(slot, spelling, command);
    }
    // An equation whose function context reads the configuration leaves, where it does not
    // apply, its application with the configuration it read, which the generator does not state.
    if undriven(slot).is_some()
        || matches!(slot.form, "desugar" | "alias")
        || (slot.form, slot.position) == ("equation", "context-map-key")
    {
        return Vec::new();
    }
    let mut drivers = spelling
        .counter
        .clone()
        .unwrap_or_default()
        .into_iter()
        .map(|counter| Driver::new(slot, spelling, command, Some(counter), false))
        .collect::<Vec<_>>();
    // An equation's counter run is read by the application it leaves, which the generator
    // states only where the equation reads no configuration.
    if !matches!(slot.form, "equation" | "table")
        && let Some(x) = &spelling.x_counter
    {
        drivers.push(Driver {
            x: Some(x.clone()),
            ..Driver::new(slot, spelling, command, Some(x.clone()), false)
        });
    }
    if matches!(
        slot.opener,
        Some("set-element" | "set-element-beside-fresh")
    ) {
        drivers.push(Driver::new(slot, spelling, command, None, true));
    }
    drivers
        .into_iter()
        .filter_map(|driver| {
            let K7::Run(mut run) = driver.plan().ok()? else {
                return None;
            };
            if driver.counter.is_some() && !driver.read_witness.get() {
                return None;
            }
            if matches!(slot.form, "equation" | "table") {
                return Some(run);
            }
            run.steps = run.steps.checked_sub(1)?;
            run.cells = Vec::new();
            run.status = Status::Liveness;
            Some(run)
        })
        .collect()
}

/// A static clause's counter runs ([`counter_plans`]).
fn static_counter_plans(slot: &Slot, spelling: &Spelling, command: &Command) -> Vec<Run> {
    let mut runs = spelling
        .counter
        .clone()
        .unwrap_or_default()
        .into_iter()
        .filter_map(|counter| {
            let K7::Run(mut run) = Driver::new(slot, spelling, command, Some(counter), false)
                .plan()
                .ok()?
            else {
                return None;
            };
            run.cells = Vec::new();
            run.status = Status::Unexpanded;
            Some(run)
        })
        .collect::<Vec<_>>();
    let Ok(witness) = spelling.witness.as_ref() else {
        return runs;
    };
    for second in second_spellings(witness) {
        runs.push(Run {
            program: format!("{}(1, {second})", command.terminal()),
            variables: Vec::new(),
            depth: 0,
            steps: 0,
            cells: vec![("k".to_owned(), Ground::Seq(vec![hold(int(1))]))],
            status: Status::Liveness,
            forward_only: base_forward_only(),
        });
    }
    for other in neighbour_values(witness) {
        runs.push(Run {
            program: format!("{}(1, {other})", command.terminal()),
            variables: Vec::new(),
            depth: 0,
            steps: 0,
            cells: Vec::new(),
            status: Status::Unexpanded,
        });
    }
    runs
}

/// The counter runs of a subject beside a second clause of its production
/// (`DESUGAR_SUBJECT_BESIDE`): those of the subject alone ([`static_counter_plans`]), and the
/// program the second clause's subject matches, `NAME(1, pair(7, 7))`, which that clause expands
/// to `pair(1, 1)`, the case's own clause not matching it.
fn beside_plans(slot: &Slot, spelling: &Spelling, command: &Command) -> Vec<Run> {
    let mut runs = static_counter_plans(slot, spelling, command);
    runs.push(Run {
        program: format!("{}(1, pair(7, 7))", command.terminal()),
        variables: Vec::new(),
        depth: 0,
        steps: 0,
        cells: vec![("k".to_owned(), Ground::Seq(vec![pair(int(1), int(1))]))],
        status: Status::Liveness,
    });
    runs
}

/// The program spellings of the builtin token `witness`'s value other than the one K7 writes
/// ([`second_spelling`]), and for a binary64 `Float` written with a fraction also its value in
/// exponent form (`15e-1`), with the binary64 suffix `d` (`1.5d`) and with binary64's
/// precision and exponent range spelled out (`1.5p53x11`): every one the same term, which the
/// clause must expand.
fn second_spellings(witness: &Ground) -> Vec<String> {
    let mut spellings = second_spelling(witness).into_iter().collect::<Vec<_>>();
    if let Some((sign, whole, fraction)) = decimal_float(witness) {
        let digits = format!("{whole}{fraction}");
        spellings.push(format!("{sign}{digits}e-{}", fraction.len()));
        spellings.push(format!("{sign}{whole}.{fraction}d"));
        spellings.push(format!("{sign}{whole}.{fraction}p53x11"));
    }
    spellings
}

/// Spellings of values next to the builtin token `witness`'s, which name other values: for a
/// binary64 `Float` written with a fraction, the same digits in binary32 (`1.5f`), and at zero
/// the zero of the other sign (`-0.0` beside `0.0`): a float's format and its sign at zero are
/// part of its value, so the clause must leave each unexpanded.
fn neighbour_values(witness: &Ground) -> Vec<String> {
    let Some((sign, whole, fraction)) = decimal_float(witness) else {
        return Vec::new();
    };
    let mut values = vec![format!("{sign}{whole}.{fraction}f")];
    if format!("{whole}{fraction}")
        .bytes()
        .all(|byte| byte == b'0')
    {
        let other = if sign.is_empty() { "-" } else { "" };
        values.push(format!("{other}{whole}.{fraction}"));
    }
    values
}

/// The sign, whole digits and fraction digits of a `Float` witness K7 writes as a plain
/// decimal with a fraction (`-2.25`); `None` for any other term or spelling.
fn decimal_float(witness: &Ground) -> Option<(&str, &str, &str)> {
    let Ground::Float(text) = witness else {
        return None;
    };
    let (sign, unsigned) = text
        .strip_prefix('-')
        .map_or(("", text.as_str()), |rest| ("-", rest));
    let (whole, fraction) = unsigned.split_once('.')?;
    (!whole.is_empty()
        && !fraction.is_empty()
        && whole
            .bytes()
            .chain(fraction.bytes())
            .all(|byte| byte.is_ascii_digit()))
    .then_some((sign, whole, fraction))
}

/// A program spelling of the builtin token `witness` other than the one K7 writes
/// ([`Ground::literal_program`]), of the same value: an `Int` with a leading zero (`01`, `-01`),
/// a `Float` with a trailing zero in its fraction (`1.50`), a `String` with every character
/// escaped (`"\x73"`), and a `Bytes` value with every byte escaped (`b"\x61\x62"`). `None` where
/// no other spelling of the value differs: a `Bool` (`true` and `false` are the only texts of
/// their values), a token of a sort without a builtin hook (its text is its value), a `Bytes`
/// value K7 already writes escaped byte by byte, and every other term.
fn second_spelling(witness: &Ground) -> Option<String> {
    use std::fmt::Write as _;
    let second = match witness {
        Ground::Int(value) if *value < 0 => format!("-0{}", value.unsigned_abs()),
        Ground::Int(value) => format!("0{value}"),
        Ground::Float(text)
            if text.contains('.')
                && text
                    .bytes()
                    .all(|byte| byte.is_ascii_digit() || b"-.".contains(&byte)) =>
        {
            format!("{text}0")
        }
        Ground::String(text) => {
            let mut written = String::from("\"");
            for character in text.chars() {
                match u32::from(character) {
                    code @ 0..=0xff => write!(written, "\\x{code:02x}"),
                    code @ 0x100..=0xffff => write!(written, "\\u{code:04x}"),
                    code => write!(written, "\\U{code:08x}"),
                }
                .expect("writing to a String cannot fail");
            }
            written.push('"');
            written
        }
        Ground::Bytes(bytes) => {
            let mut written = String::from("b\"");
            for byte in bytes {
                write!(written, "\\x{byte:02x}").expect("writing to a String cannot fail");
            }
            written.push('"');
            written
        }
        _ => return None,
    };
    (Some(second.as_str()) != witness.literal_program().as_deref()).then_some(second)
}

impl<'a> Driver<'a> {
    fn new(
        slot: &'a Slot,
        spelling: &'a Spelling,
        command: &'a Command,
        counter: Option<Ground>,
        extra: bool,
    ) -> Self {
        Self {
            slot,
            spelling,
            command,
            counter,
            extra,
            x: None,
            read_witness: Cell::new(false),
        }
    }

    /// Whether the driver runs a counter-witness: one of the spelling's, or an item more.
    const fn countering(&self) -> bool {
        self.counter.is_some() || self.extra
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
        if let Some(counter) = &self.counter {
            return Ok(counter.clone());
        }
        self.spelling
            .witness
            .clone()
            .map_err(|reason| K7::skip(SkipKind::Witness, reason))
    }

    /// A set's element where a pattern reads it, which reads as a key does (decision D2): the
    /// spelling's value, looked up, where it denotes one, and its witness otherwise.
    fn element(&self) -> Read {
        if self.counter.is_none()
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
        // The set's singleton around the hole is exact: in extra mode it holds an element more.
        let singleton = |element: Ground| {
            let mut elements = vec![element];
            if self.extra {
                elements.push(int(EXTRA));
            }
            Ground::set(elements)
        };
        if self.slot.opener == Some("set-element") {
            let element = self.element()?;
            return Ok(Hole {
                term: singleton(element.term),
                status: element.status,
            });
        }
        let witness = self.own_witness()?;
        let term = match self.slot.opener {
            // A counter-witness `Cmd::Go()` would match the other alternative.
            Some("or-branch") if self.countering() && witness == go() => {
                return Err(K7::skip(
                    SkipKind::Witness,
                    "the counter-witness is the other alternative, Cmd::Go()",
                ));
            }
            None | Some("as-body" | "or-branch" | "rewrite-left") => witness,
            Some("argument") => Ground::ctor("Cmd::Hold", vec![witness]),
            // `z`, a name nothing else binds, is any term: 0.
            Some("beside-fresh") => pair(witness, int(0)),
            Some("set-element-beside-fresh") => singleton(pair(witness, int(0))),
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
        let x_value = self.x.clone().map(Meaning::Value);
        let spelling = x_value.as_ref().unwrap_or(&self.spelling.value);
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
        // An x-counter is read where the hole is looked up: the key a reading that ignored the
        // hole's meaning would compute from `x`.
        if self.x.is_some() {
            self.read_witness.set(true);
        }
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
            forward_only: base_forward_only(),
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

    /// A run that adds `other` and then `setup`, one step each, and then applies the case's
    /// sentence to `command`: `then(then(other, setup), command)`, five steps that leave the
    /// computation cell empty.
    fn set_up_beside(
        other: Ground,
        setup: Ground,
        command: Ground,
        status: Status,
    ) -> Result<K7, K7> {
        let program = Ground::ctor(
            "Cmd::Then",
            vec![Ground::ctor("Cmd::Then", vec![other, setup]), command],
        );
        Self::applied(&program, 5, vec![("k", Ground::Seq(Vec::new()))], status)
    }

    /// The plan of the case.
    #[expect(
        clippy::too_many_lines,
        reason = "One match of the closed slot set; each arm is one slot's driver."
    )]
    fn plan(&self) -> Result<K7, K7> {
        // `x`'s value: 1, or an x-counter's.
        let one = || self.x.clone().unwrap_or_else(|| int(1));
        let k = |items: Vec<Ground>| ("k", Ground::Seq(items));
        let fields = |a: Ground, b: Ground| vec![a, b];
        // The case's command over `x` = 1 and a second field the template does not read.
        let reading = || self.command(fields(one(), int(0)));
        let call =
            |argument: Ground| Ground::ctor("Cmd::Call", vec![self.command(Vec::new()), argument]);
        let setup = |command: &str, arguments: Vec<Ground>| {
            Ground::ctor(&format!("Cmd::{command}"), arguments)
        };
        // A map the slot reads with `..`: the entry the case reads, and one more.
        let env = |key: Ground, value: Ground| {
            setup(
                "SetEnv",
                vec![Ground::map(vec![(key, value), (int(EXTRA), int(0))])],
            )
        };
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
            ("rule" | "sort-rule", "subject-root" | "subject-root-term")
            | ("rule", "subject-root-list") => {
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
            // A rule whose result restates its subject: the step leaves the command as it was.
            ("cells", "guard-restated") => self.guarded(
                &reading(),
                1,
                vec![k(vec![reading()])],
                vec![k(vec![reading()])],
            ),
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
                        (
                            "env",
                            Ground::map(vec![(one(), value.term), (int(EXTRA), int(0))]),
                        ),
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
                let list = setup(
                    "SetStack",
                    vec![Ground::List(vec![witness.term, int(EXTRA)])],
                );
                Self::set_up(list, reading(), vec![k(empty_items())], witness.status)
            }
            ("readable", "cons-element") => {
                let witness = self.witness()?;
                let items = Ground::ctor(
                    "Seq::Cons",
                    vec![
                        witness.term,
                        Ground::ctor(
                            "Seq::Cons",
                            vec![int(EXTRA), Ground::ctor("Seq::Nil", Vec::new())],
                        ),
                    ],
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
            // The collection holds another instance, added first (behind the case's in the List
            // collection), which the case's `..` leaves.
            ("readable", "collection-child" | "set-instance-child") => {
                let (witness, command) = if position == "collection-child" {
                    (self.witness()?, "AddMember")
                } else {
                    (self.element()?, "AddToken")
                };
                Self::set_up_beside(
                    setup(command, vec![go()]),
                    setup(command, vec![hold(witness.term)]),
                    reading(),
                    witness.status,
                )
            }
            // Another row, keyed by `pair(99, 99)`, which no case's key is.
            ("readable", "map-key-child" | "map-value-child") => {
                let witness = self.witness()?;
                let row = if position == "map-key-child" {
                    vec![hold(witness.term), go()]
                } else {
                    vec![go(), hold(witness.term)]
                };
                Self::set_up_beside(
                    setup("AddRow", vec![pair(int(EXTRA), int(EXTRA)), go()]),
                    setup("AddRow", row),
                    reading(),
                    witness.status,
                )
            }
            // `stack: [_, ..]` read and `stack: [HOLE, ..]` written: the stack starts as `[0, 99]`,
            // whose rest the result keeps.
            ("readable", "result-list-element") => {
                let value = self.value()?;
                Self::set_up(
                    setup("SetStack", vec![Ground::List(vec![int(0), int(EXTRA)])]),
                    reading(),
                    vec![
                        k(empty_items()),
                        ("stack", Ground::List(vec![value.term, int(EXTRA)])),
                    ],
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
                let result = if self.countering() {
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
            // `Probe(Cmd::NAME(), x)` with the key its function context looks up in the map:
            // the call's result is 0 where the equation applies.
            ("equation", "context-map-key") => {
                let key = self.key()?;
                Self::set_up(
                    env(key.term, int(0)),
                    call(one()),
                    vec![k(vec![hold(int(0))])],
                    key.status,
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
            // The case's rule writes the clause's production applied to the witness, which
            // kompile expanded: `drive(N)` takes one step to the clause's result.
            ("desugar" | "alias", "subject-written") => {
                let witness = self.witness()?;
                super::written(&witness.term).ok_or_else(|| {
                    K7::skip(
                        SkipKind::Witness,
                        format!("no rule writes {} as one term", witness.term),
                    )
                })?;
                self.forward_only_if_unread(Self::applied(
                    &Ground::ctor("Cmd::Drive", vec![int(i64::from(self.command.drive()))]),
                    1,
                    vec![k(vec![hold(one())])],
                    witness.status,
                ))
            }
            // A static clause expands what a program writes as `krs run` parses it: no step.
            ("desugar" | "alias", "subject" | "subject-typed") | ("desugar", "subject-beside") => {
                let witness = self.witness()?;
                literal(&witness.term)?;
                self.forward_only_if_unread(Self::expanded(
                    &self.command(fields(one(), witness.term)),
                    vec![k(vec![hold(one())])],
                    witness.status,
                ))
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
                self.forward_only_if_computed(Self::expanded(
                    &self.command(vec![one()]),
                    vec![k(vec![value.term])],
                    value.status,
                ))
            }
            ("alias", "result-root-ground") => {
                let value = self.value()?;
                self.forward_only_if_computed(Self::expanded(
                    &self.command(Vec::new()),
                    vec![k(vec![value.term])],
                    value.status,
                ))
            }
            ("alias", "result") => {
                let value = self.value()?;
                self.forward_only_if_computed(Self::expanded(
                    &self.command(vec![one()]),
                    vec![k(vec![pair(one(), value.term)])],
                    value.status,
                ))
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

    /// `plan`, with the case's own command among the aliases no print writes where the case's
    /// spelling, which stands in its alias clause's result, computes.
    fn forward_only_if_computed(&self, mut plan: Result<K7, K7>) -> Result<K7, K7> {
        if let Ok(K7::Run(run)) = &mut plan
            && self
                .spelling
                .nodes
                .iter()
                .any(|node| computes(node.construct))
        {
            run.forward_only.push(self.command.name.clone());
        }
        plan
    }

    /// `plan`, with the case's own command among the aliases no print writes where its alias
    /// clause's subject holds a token whose printed text no program reads back as it: the `Id`
    /// `$x` (`k::id!("$x")`), which a program writes only through its maker, so printed as `$x`
    /// it lexes as no token at all.
    fn forward_only_if_unread(&self, mut plan: Result<K7, K7>) -> Result<K7, K7> {
        if let Ok(K7::Run(run)) = &mut plan
            && self.slot.form == "alias"
            && self
                .spelling
                .nodes
                .iter()
                .any(|node| node.construct == Construct::IdToken)
        {
            run.forward_only.push(self.command.name.clone());
        }
        plan
    }
}

/// The base's aliases whose clauses' written results compute: `an => hold(1 - 1)`.
fn base_forward_only() -> Vec<String> {
    vec!["An".to_owned()]
}

/// Whether `construct`, where a term is built, computes it rather than writing it: an
/// application of a function or a builtin operation, a notation form that applies an operation,
/// a set's concatenation (the union of its parts), `let`, `k::matches!`, `k::or_bool!`, a sort
/// test or a record update. A name, a constructor's application, a literal, a token, list brackets and a
/// collection's unit or singleton write the term they denote.
///
/// List brackets hold at most one rest (`[a, ..mid, z]`), so the term they write splits a list
/// value one way, and they construct. A list concatenation that joins two named lists, which
/// only `k::builtin::list::concat` writes, computes, since the value it matches has several
/// splits; the spellings write `list::concat` nowhere, and a builtin operation's application
/// counts as computing here (the product tells `list::concat(list::item(x), rest)`, which
/// constructs, by its operands).
const fn computes(construct: Construct) -> bool {
    match construct {
        Construct::FunctionApplication
        | Construct::BuiltinApplication
        | Construct::Concatenation
        | Construct::Let
        | Construct::Matches
        | Construct::SortTest
        | Construct::OrBool
        | Construct::RecordUpdate => true,
        Construct::Notation(notation) => notation.applies_operation(),
        Construct::Reference
        | Construct::Fresh
        | Construct::Constructor
        | Construct::StaticApplication
        | Construct::OpenStaticApplication
        | Construct::Turbofish
        | Construct::Literal
        | Construct::CollectionValue
        | Construct::Wildcard
        | Construct::As
        | Construct::Or
        | Construct::MlPredicate
        | Construct::Rewrite
        | Construct::Anonymous
        | Construct::Fragment
        | Construct::OpenRecord
        | Construct::ListBrackets
        | Construct::Rest
        | Construct::IdToken
        | Construct::BytesToken
        | Construct::Lexeme => false,
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
