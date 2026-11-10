//! What a lock entry depends on that the clock stopped (FB45-LOCKED-TIMEOUT; README, "What
//! decides a verdict").
//!
//! A lock entry must be a function of the definition, the corpus, the record before the run and
//! the counted budgets, never of the host's load. `budget.time_ms` is a wall clock: a run it stops
//! has no outcome, only a cancellation, and on a faster host the same run could have ended with any
//! outcome. So an entry is decided on this host only when it would be the same whatever each run
//! the clock stopped would have given, and a run the clock stopped changes no recorded entry
//! ([`keep`]): the lock keeps the recorded value, `--locked` reports the entry as not decided on
//! this host (lock status `undecided`, exit 3) rather than as a difference, and a run without
//! `--locked` writes the recorded value back, saying that it kept it unverified.
//!
//! The runs the clock stops are a program's baseline run, which is then `timeout` (or `unknown`
//! with the watchdog named in its `not_cached`), so the program is not comparable and cannot
//! kill or cover anything; a program's run on a mutant, whose executed entry is `timeout`; and an
//! argued item's evidence run of a program, which the item's evidence names
//! (`argument_check.evidence.clock_stopped`, from kink-campaign's `RunStop::Time`), and which
//! leaves the evidence unread there.
//!
//! What a mutation's (or a flip's) entry depends on follows from the killer rule (README, "The
//! corpus record"), with k the recorded killer and C the search order:
//!
//! - A status decided before any run (`equivalent`, `unkillable`, a refusal, an `error`) depends
//!   on no run.
//! - A kill by k (rule 1) depends on no other run: k's run ended and distinguished.
//! - Any other kill is still a kill, a function of the inputs, since the program that killed
//!   ended; but which program is the killer depends on k's run when the clock stopped it (rule 1
//!   could have held), on every program before the killer in C whose run on the mutant the clock
//!   stopped, and on every program whose baseline the clock stopped (it would be in the corpus's
//!   comparable programs, at a place in C its coverage would give).
//! - Every other status (a survivor, an `unknown`, a `timeout`) depends on every program whose
//!   run on the mutant or baseline the clock stopped: each could have killed.
//!
//! A recorded entry is kept where the entry depends on a stopped run, unless the run decided a
//! fact the recorded entry contradicts: a kill where the lock records none (a recorded survivor,
//! `unknown` or `timeout` now killed by a program that ended), a recorded status no run could give
//! (a refusal, `equivalent`), or no recorded entry at all, where the run's own row is written.
//!
//! A coverage lock's obligations are existential over the comparable programs: an obligation is
//! covered when some comparable program covers it. A covered obligation is decided; one that is
//! not covered depends on every program whose baseline the clock stopped, which could have covered
//! it. So where such a program exists an obligation the lock does not list (covered when it was
//! written) and that shows open, argued or undecided now is kept unlisted, and one the lock lists
//! undecided that shows open is kept undecided; an obligation the lock lists open or argued and
//! that a program that ended now covers, or whose argument the manifest added or removed, has
//! moved. An argued item's standing rests on the evidence of the comparable programs' runs, so
//! it is kept too where it moved, unless either side is `text`, which no run decides; and so is
//! a standing one of whose own evidence runs the clock stopped, where every baseline ended. A lock does
//! not tell an obligation it recorded covered from one that was no obligation when it was written,
//! so after a definition edit on a host whose clock stops a program, a new obligation that shows
//! open stays unlisted until a host that runs every program writes the lock.

use crate::{
    coverage::{ARGUABLE, ARGUED, FAMILIES, STANDING_TEXT, UNDECIDED},
    flips,
    lock::{Lock, LockKind},
    results::ResultClass,
};
use serde_json::{Map, Value, json};
use std::collections::BTreeMap;

/// What the clock stopped of a document's runs, and the document whose rendering the lock is
/// compared with and written as ([`keep`]).
#[derive(Debug)]
pub struct Kept {
    /// The document with each kept entry's recorded value in place of the one the run gave.
    pub document: Value,
    /// The runs the clock stopped that some entry depends on (`lock.clock_stopped`):
    /// `{program, run: "baseline"}`, once per program, `{program, run: "mutant", <row>: id}`
    /// per row whose entry depends on that run, and `{program, run: "evidence", argument: id}`
    /// per argued item whose evidence run of that program the clock stopped.
    pub stopped: Vec<Value>,
    /// Each entry whose recorded value the lock keeps over a different one a stopped run decided
    /// (`lock.kept`): `{<row>: id, recorded, now}` for a mutation or a flip (each side `{status,
    /// killer, reason}`), `{family, obligation, recorded, now}` for an obligation (each side
    /// `"open"`, `"argued"`, `"undecided"` or null where that side lists it neither way), and
    /// `{argument, recorded, now}` for an argued item's standing.
    pub kept: Vec<Value>,
}

/// Whether the clock stopped a program's baseline run: its class is `timeout`, or its
/// `not_cached` says the watchdog stopped the run (an `unknown` whose class then came from a
/// diagnostic run).
#[must_use]
pub fn baseline_stopped(row: &Value) -> bool {
    row["class"] == ResultClass::Timeout.as_str()
        || row["not_cached"]
            .as_str()
            .is_some_and(|reason| reason.contains(crate::results::WATCHDOG_STOPPED))
}

/// The programs a run row's executed entries name whose run on the mutant the clock stopped
/// (outcome or slot `timeout`), in the row's order.
#[must_use]
pub fn mutant_timeouts(row: &Value) -> Vec<String> {
    row["executed"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|entry| {
            entry["outcome"] == "timeout"
                || entry["slots"]
                    .as_object()
                    .is_some_and(|slots| slots.values().any(|slot| slot["outcome"] == "timeout"))
        })
        .filter_map(|entry| entry["program"].as_str().map(str::to_owned))
        .collect()
}

/// `document` with each entry that depends on a run the clock stopped given its recorded value
/// from `lock`, with the stopped runs and the kept entries (module documentation).
#[must_use]
pub fn keep(lock: &Lock, document: &Value) -> Kept {
    let mut kept = Kept {
        document: document.clone(),
        stopped: Vec::new(),
        kept: Vec::new(),
    };
    let programs = document["programs"]
        .as_array()
        .map_or(&[][..], Vec::as_slice);
    let baseline = programs
        .iter()
        .filter(|row| baseline_stopped(row))
        .filter_map(|row| row["id"].as_str())
        .collect::<Vec<_>>();
    let comparable = programs
        .iter()
        .filter(|row| ResultClass::can_kill(&row["class"]))
        .filter_map(|row| row["id"].as_str())
        .collect::<Vec<_>>();
    let recorded = recorded_rows(lock);
    let mut on_baseline = false;
    let kind = lock.kind;
    let rows = match kind {
        LockKind::Run => items_mut(&mut kept.document, "/mutations"),
        LockKind::Coverage => items_mut(&mut kept.document, "/families/flips/items"),
    };
    for row in rows.into_iter().flatten() {
        let Some(id) = row["id"].as_str().map(str::to_owned) else {
            continue;
        };
        let record = lock.rows.iter().find(|row| row.id == id);
        let killer = record.and_then(|row| row.killer.as_deref());
        let Some(stops) = row_stops(kind, row, killer, &comparable) else {
            continue;
        };
        if stops.is_empty() && baseline.is_empty() {
            continue;
        }
        on_baseline |= !baseline.is_empty();
        for program in &stops {
            kept.stopped
                .push(json!({"program": program, "run": "mutant", kind.row(): id}));
        }
        let Some(record) = record else {
            continue;
        };
        let killed = kill_status(kind);
        let status = record.status.as_deref().unwrap_or_default();
        let keepable = status == killed || dependent_statuses(kind).contains(&status);
        if !keepable || (row["status"] == killed && status != killed) {
            continue;
        }
        let horizon = recorded
            .get(id.as_str())
            .map_or(Value::Null, |row| horizon_value(&row["horizon"]));
        let now = now_value(kind, row);
        let before = json!({"status": record.status, "killer": record.killer,
                            "reason": record.reason});
        if now != before || row["horizon"] != horizon {
            kept.kept
                .push(json!({kind.row(): id, "recorded": before, "now": now}));
        }
        row["status"] = json!(record.status);
        row["killer"] = json!(record.killer);
        row["reason"] = json!(record.reason);
        row["horizon"] = horizon;
    }
    if kind == LockKind::Coverage {
        if !baseline.is_empty() {
            on_baseline = true;
            if lock.records() {
                keep_obligations(lock, &mut kept);
            }
        }
        keep_standings(lock, &mut kept, !baseline.is_empty());
    }
    if on_baseline {
        let stops = baseline
            .iter()
            .map(|program| json!({"program": program, "run": "baseline"}));
        kept.stopped.splice(0..0, stops);
    }
    kept
}

/// The array at `pointer` in `document`, where there is one. Indexing a `Value` mutably would
/// insert each missing key, and a family the document did not build would then render.
fn items_mut<'d>(document: &'d mut Value, pointer: &str) -> Option<&'d mut Vec<Value>> {
    document.pointer_mut(pointer)?.as_array_mut()
}

/// The status of a kill: a mutation's `killed`, a flip's `distinguished`.
const fn kill_status(kind: LockKind) -> &'static str {
    match kind {
        LockKind::Run => "killed",
        LockKind::Coverage => flips::DISTINGUISHED,
    }
}

/// The statuses other than a kill that a run decides, so that a stopped run could have given
/// another: a mutation's survivor, `unknown` and `timeout`; a flip's undistinguished, unreached
/// (no comparable program reached it), argued and `unknown` ones.
const fn dependent_statuses(kind: LockKind) -> &'static [&'static str] {
    match kind {
        LockKind::Run => &["survived", "unknown", "timeout"],
        LockKind::Coverage => &[
            flips::UNDISTINGUISHED,
            flips::UNREACHED,
            ARGUED,
            flips::UNKNOWN,
        ],
    }
}

/// The programs whose run on the mutant the clock stopped and that the row's entry depends on
/// (module documentation), with `killer` the recorded killer and `comparable` the comparable
/// programs in corpus order; `None` where the entry depends on no run at all (a status decided
/// before any run, or a kill by the recorded killer), so that no baseline the clock stopped
/// matters either.
fn row_stops(
    kind: LockKind,
    row: &Value,
    killer: Option<&str>,
    comparable: &[&str],
) -> Option<Vec<String>> {
    let status = row["status"].as_str().unwrap_or_default();
    let killed = status == kill_status(kind);
    // A flip's `unknown` stands for every status kink gave no verdict by; only a survivor's,
    // an unknown's and a timeout's depend on runs.
    let dependent = match kind {
        LockKind::Run => dependent_statuses(kind).contains(&status),
        LockKind::Coverage => {
            (status != flips::UNKNOWN && dependent_statuses(kind).contains(&status))
                || matches!(row["kink_status"].as_str(), Some("unknown" | "timeout"))
        }
    };
    if !(killed || dependent) {
        return None;
    }
    if killed && killer.is_some() && row["killer"].as_str() == killer {
        return None;
    }
    let timeouts = match kind {
        LockKind::Run => mutant_timeouts(row),
        LockKind::Coverage => row["timed_out"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .map(str::to_owned)
            .collect(),
    };
    if !killed {
        return Some(timeouts);
    }
    // The search order C: the programs that witness the edit first, then the rest, each in
    // corpus order (README, "The corpus record"; every program when no witness is known).
    let witnesses = row["witnesses"].as_array();
    let place = |program: &str| {
        let witness = witnesses.is_none_or(|ids| ids.iter().any(|id| id == program));
        let index = comparable.iter().position(|id| *id == program);
        (!witness, index.unwrap_or(usize::MAX))
    };
    let at = place(row["killer"].as_str().unwrap_or_default());
    Some(
        timeouts
            .into_iter()
            .filter(|program| Some(program.as_str()) == killer || place(program) < at)
            .collect(),
    )
}

/// What a lock compares of a row of either kind, `{status, killer, reason}`.
fn now_value(kind: LockKind, row: &Value) -> Value {
    match kind {
        LockKind::Run => json!({
            "status": row["status"],
            "killer": if row["status"] == "killed" { row["killer"].clone() } else { Value::Null },
            "reason": crate::verdicts::rendered_reason(row),
        }),
        LockKind::Coverage => {
            let rendered = crate::verdicts::rendered_flip(row);
            json!({"status": rendered["status"], "killer": rendered["killer"],
                   "reason": rendered["reason"]})
        }
    }
}

/// The command's recorded rows by id, as TOML read into JSON ([`Lock::recorded_table`]): the
/// source of a kept row's `horizon`, which [`Lock`] does not decode. Empty where nothing is
/// recorded.
fn recorded_rows(lock: &Lock) -> BTreeMap<String, Value> {
    let Some(table) = lock.recorded_table() else {
        return BTreeMap::new();
    };
    table
        .get(lock.kind.row())
        .and_then(toml::Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(|row| {
            let id = row.get("id")?.as_str()?.to_owned();
            Some((id, serde_json::to_value(row).ok()?))
        })
        .collect()
}

/// A recorded row's `horizon` (one `{program, channel, elements, opening}` per line) as a run row
/// holds it, `[{program, horizon: {<channel>: {elements, opening}}}]`, so that the rendering
/// writes it back as it was; null where the row has none.
fn horizon_value(recorded: &Value) -> Value {
    let Some(entries) = recorded.as_array() else {
        return Value::Null;
    };
    let mut horizons: Vec<(String, Map<String, Value>)> = Vec::new();
    for entry in entries {
        let program = entry["program"].as_str().unwrap_or_default().to_owned();
        let channel = entry["channel"].as_str().unwrap_or_default().to_owned();
        let at = json!({"elements": entry["elements"], "opening": entry["opening"]});
        match horizons.last_mut() {
            Some((last, channels)) if *last == program => {
                channels.insert(channel, at);
            }
            _ => horizons.push((program, Map::from_iter([(channel, at)]))),
        }
    }
    json!(
        horizons
            .into_iter()
            .map(|(program, channels)| json!({"program": program, "horizon": channels}))
            .collect::<Vec<_>>()
    )
}

/// A coverage section's undecided obligations by family (`[coverage.rules] undecided`, ...), which
/// [`Lock`] does not decode.
fn recorded_undecided(lock: &Lock) -> BTreeMap<String, Vec<String>> {
    let Some(table) = lock.recorded_table() else {
        return BTreeMap::new();
    };
    FAMILIES
        .iter()
        .filter_map(|family| {
            let ids = table.get(*family)?.get(UNDECIDED)?.as_array()?;
            let ids = ids
                .iter()
                .filter_map(|id| id.as_str().map(str::to_owned))
                .collect();
            Some(((*family).to_owned(), ids))
        })
        .collect()
}

/// Keep each obligation the lock does not list that shows open, argued or undecided now, and
/// each the lock lists undecided that shows open: a program whose baseline the clock stopped
/// could have covered it (module documentation).
fn keep_obligations(lock: &Lock, kept: &mut Kept) {
    let undecided = recorded_undecided(lock);
    for family in FAMILIES.iter().filter(|family| **family != "flips") {
        // A family the lock does not record (another depth) is the header's difference.
        if !lock.open.contains_key(*family) {
            continue;
        }
        let listed = |ids: Option<&Vec<String>>, id: &str| {
            ids.is_some_and(|ids| ids.iter().any(|i| i == id))
        };
        let Some(items) = items_mut(&mut kept.document, &format!("/families/{family}/items"))
        else {
            continue;
        };
        for item in items {
            let Some(id) = item["id"].as_str().map(str::to_owned) else {
                continue;
            };
            let now = if item["status"] == ARGUED {
                ARGUED
            } else if item["status"] == UNDECIDED {
                UNDECIDED
            } else if item["covered"] == false {
                "open"
            } else {
                continue;
            };
            let before = if listed(lock.open.get(*family), &id) {
                Some("open")
            } else if listed(lock.argued.get(*family), &id) {
                Some(ARGUED)
            } else if listed(undecided.get(*family), &id) {
                Some(UNDECIDED)
            } else {
                None
            };
            match before {
                None => {
                    item["covered"] = json!(true);
                    if now != "open" {
                        item["status"] = json!("covered");
                    }
                }
                Some(UNDECIDED) if now == "open" => item["status"] = json!(UNDECIDED),
                _ => continue,
            }
            kept.kept.push(json!({"family": family, "obligation": id,
                                  "recorded": before, "now": now}));
        }
    }
}

/// Keep each argued item's recorded standing where it moved and the standing depends on a run
/// the clock stopped: a baseline (`baseline`), since the evidence reads the comparable programs'
/// runs, or one of the item's own evidence runs (`argument_check.evidence.clock_stopped`), each
/// of which a stopped run leaves unread. A `text` standing rests on no run (module
/// documentation).
fn keep_standings(lock: &Lock, kept: &mut Kept, baseline: bool) {
    let now = crate::coverage::argument_standings(&kept.document)
        .into_iter()
        .collect::<BTreeMap<_, _>>();
    let text = |standing: &str| standing.split(',').next() == Some(STANDING_TEXT);
    for family in ARGUABLE {
        let items = items_mut(&mut kept.document, &format!("/families/{family}/items"));
        for item in items.into_iter().flatten() {
            let Some(id) = item["id"].as_str().map(str::to_owned) else {
                continue;
            };
            let Some(standing) = now.get(&id).filter(|_| item["status"] == ARGUED) else {
                continue;
            };
            let evidence = item["argument_check"]["evidence"]["clock_stopped"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
                .map(str::to_owned)
                .collect::<Vec<_>>();
            if text(standing) || (!baseline && evidence.is_empty()) {
                continue;
            }
            for program in evidence {
                kept.stopped
                    .push(json!({"program": program, "run": "evidence", "argument": id}));
            }
            let Some(recorded) = lock.arguments.get(&id) else {
                continue;
            };
            if recorded == standing || text(recorded) {
                continue;
            }
            // The standing as the lock spells it, assumed findings included.
            item["argument_check"] = json!({"standing": recorded});
            kept.kept
                .push(json!({"argument": id, "recorded": recorded, "now": standing}));
        }
    }
}

/// The lines `kink-flow` prints on stderr for a lock some entry of which depends on a run the
/// clock stopped: one per stopped run, then one per kept entry (`lock.clock_stopped`,
/// `lock.kept`); empty otherwise.
#[must_use]
pub fn clock_lines(document: &Value) -> Vec<String> {
    let lock = &document["lock"];
    let kind = if document["schema"] == crate::coverage::COVERAGE_SCHEMA {
        LockKind::Coverage
    } else {
        LockKind::Run
    };
    let path = lock["path"].as_str().unwrap_or(crate::lock::LOCK_FILE);
    let text = |value: &Value| value.as_str().unwrap_or("?").to_owned();
    let mut lines = Vec::new();
    for stop in lock["clock_stopped"].as_array().into_iter().flatten() {
        let program = text(&stop["program"]);
        lines.push(if stop["run"] == "baseline" {
            format!(
                "{path}: the clock (budget.time_ms) stopped the baseline run of {program}: what \
                 depends on it is not decided on this host"
            )
        } else if stop["run"] == "evidence" {
            format!(
                "{path}: arguments: {}: the clock (budget.time_ms) stopped the evidence run of \
                 {program}: its standing is not decided on this host",
                text(&stop["argument"])
            )
        } else {
            format!(
                "{path}: {}: the clock (budget.time_ms) stopped the run of {program} on its \
                 mutant: its entry is not decided on this host",
                text(&stop[kind.row()])
            )
        });
    }
    let verdict = |side: &Value| match side["killer"].as_str() {
        Some(killer) => format!("{} (killer {killer})", text(&side["status"])),
        None => text(&side["status"]),
    };
    let state = |side: &Value| side.as_str().unwrap_or("unlisted").to_owned();
    for entry in lock["kept"].as_array().into_iter().flatten() {
        let (what, recorded, now) = if let Some(id) = entry[kind.row()].as_str() {
            (
                id.to_owned(),
                verdict(&entry["recorded"]),
                verdict(&entry["now"]),
            )
        } else if let Some(family) = entry["family"].as_str() {
            (
                format!("{family}: {}", text(&entry["obligation"])),
                state(&entry["recorded"]),
                state(&entry["now"]),
            )
        } else {
            (
                format!("arguments: {}", text(&entry["argument"])),
                state(&entry["recorded"]),
                state(&entry["now"]),
            )
        };
        lines.push(format!(
            "{path}: {what}: kept {recorded} unverified: this host gives {now}"
        ));
    }
    lines
}
