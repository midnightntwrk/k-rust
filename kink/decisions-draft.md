# Decision register: drafts

This file holds drafts of entries and amendments for kink's decision register, [`decisions.md`](decisions.md), written in the register's format.
A draft is not normative: it decides nothing until Sebastien confirms it.
On confirmation it moves into the register with his name and date in its bracket, its paragraph "State at this draft's writing" is dropped, and it is deleted here.
Where a draft and the register disagree, the register holds.

## P. Projections

- **P1 — A corpus is measured under named projections; each has producers, one observation, a domain and a relation, and reports per case a value and its distance from the other side.**
  A flow declares its projections in `FLOW.toml` (`[[projection]]`, kink-flow README, "Projections").
  A projection has four parts:
  its producers, the sides it relates: the specification (the flow's definition, run as the flow runs it) and, optionally, an implementation (`[[implementation]]`), a mutant of the definition, or a reference value a user accepted;
  its observation, one function applied to each side's raw result and evaluated in one fixed observer: the cells compared, views of them, observation channels, the end's acceptance;
  its domain, the cases it applies to;
  and its relation, how two observed values are judged: equality, agreement up to a horizon, a measured value against a reference.
  A case is valid or invalid only relative to a projection; the corpus has no global split.
  A flow without `[[projection]]` has one projection, `default`: every observable cell of the end and every `[observe]` channel, the observation every kill compared before projections.
  `[result] cells` is replaced by a projection's `compare`, with no second spelling.
  The result record keeps the union of the cells the flow's projections compare.
  An implementation's view may name a projection; kink-flow's own K front end refuses a projection with `views` or an `observer` (O1, reason 4, as amended below).
  A command reports, per (case, projection), the observed value and its distance from the other side wherever one exists, and per projection an aggregate (cases that agree out of cases compared, survivors, open obligations).
  A pass or fail gate is a user's choice built on those outputs (`--locked`, or a threshold the user states), never a projection's only output.
  Each side's raw result is cached under that side's inputs only, and observations and relations are recomputed from it; a side whose request carries data of another side (an implementation given the specification's initial state) is keyed by that request's digest, and reruns when that data changes.
  The corpus record (the lock) holds only what kink derives and can recompute: provenance kink computes (a killer, the obligation a case discharges), digests that tell whether something must rerun, and summary counts per projection, in one section per projection.
  A reference value a user accepted (an implementation's message, a metric's baseline) is a snapshot file, `snapshots/<projection>/<case id>` beside the flow, stored as the output is (a text value as its exact text, a structured value in a deterministic pretty rendering), and is never in the lock.
  Provenance a user states (why a case exists, which tool found it) is a field of the case document.
  Several layers of one language are several flows over one corpus root; kink compares no two definitions.
  [draft, 2026-11-19, not confirmed by Sebastien: the model and its defaults were agreed with him on 2026-11-18 and 2026-11-19, and replacing `[result] cells` and the snapshot format are his decisions of 2026-11-19; this entry's wording is not confirmed]

  *State at this draft's writing.*
  kink-flow decodes `[[projection]]` (kinds `end`, `accepts` and `trace`; `metric` is refused), builds the implicit `default`, narrows the result record to the union of the projections' cells, and resolves an implementation's view that names a projection.
  A `[[projection]]` states its observation and its `domain`; its producers and relation are those of the command that reads it (`run`: the specification and its mutants, by equality and, on channels, agreement up to a horizon; `compare`: the specification and each implementation, by equality and, on a trace view, agreement up to a horizon).
  `compare` reports the distance of each end and trace view entry and each view's agreeing programs, and compares acceptance; a case document may state its `provenance`.
  Not built: `run` judges kills on one slot over the union of the projections' cells and on every `[observe]` channel, not per projection; a projection's `views` and `observer` are evaluated only where an implementation's view names the projection; an expectation does not name a projection; a view naming an `end` projection without `compare` compares every cell the implementation states, not every observable cell; `run` does not apply a projection's `domain` (`compare` does); documents do not name the projections they measured under; there are no snapshot files; the lock has one section per command.

  1. *One observation per comparison.*
     Before projections, what a comparison observes was declared in four places with overlapping keys: `[result] cells` and unobservable cells for kills, `[observe]` channels for kills and trace views, an `[[implementation]]`'s views for `compare`, and a case's `expect.views` for expectations.
     A kill and a comparison could then measure different things with nothing to show it.
     A mutant killed under the full observation may survive under the observation an implementation is held to, and that survivor is a misunderstanding the corpus cannot detect in that implementation.
     One named object per observation makes the two measurements one, and lets every command report per projection.
     Both sides of a projection are observed by one function evaluated in one fixed observer, so a difference of the observed values is a difference of the sides' results.
  2. *An optimizer needs a gradient.*
     kink builds a corpus by hill-climbing on its quality, and an implementation is improved against the corpus the same way; a yes or no outcome gives either climb nothing to follow until it flips.
     So every output carries a distance where one exists (the differing and compared cells of an end, a trace's first difference or agreeing elements, a view's agreeing programs, survivor and obligation counts), and a gate is built on the outputs by the user who wants one.
  3. *Storage follows what each value is a function of.*
     A side's raw result is a function of that side's inputs alone, so caching it under them lets another projection reuse every run and recompute only observations and relations.
     The lock is checked by recomputing it (`--locked`), so it can hold only what kink derives.
     An accepted reference value is an input of a relation, not a derivation: a value both derived and accepted would make `--locked` compare a row with itself.
     Provenance a user states cannot be recomputed, so it is an authored fact of the case.
  4. *Two definitions are related by a proof, not by a corpus.*
     A statement that one definition refines another is a claim about every run of both, not a verdict on the corpus's runs, so it belongs to the proof tool; layers of one language are flows that each measure their own definition.

  Accepted cost: a projection that compares a cell the record leaves out re-keys the baselines once; a corpus that spelled `[result] cells` rewrites it as a projection's `compare`; a projection with views or an observer runs only through a front end that reads values (`krs kink`).
  Rejected: one observation fixed in kink's code for kills beside a second family declared per implementation for comparisons (reason 1: the two can differ unseen, and the corpus is improved under one function only); a harness that sequences an agent's work (kink provides tools and documents, and an agent improving a corpus and an implementation at once chooses its own order); keeping `[result] cells` as a second spelling of the default projection (two spellings of one object, with no user to keep); a pass or fail verdict as a projection's only output (reason 2); a search over an implementation's own code inside kink (existing fuzzers search there, and kink admits the cases they find).
  Reopen on a function a user needs a corpus measured under that is not one observation applied alike to each side's raw result followed by a relation between the two observed values.

## Amendments

- **O1, reason 4 — proposed amendment: the K front end refuses a projection's views and observer too.**
  Reason 4 would read:

  4. *The K front end compares cells as they hold them.*
     kink-flow reads terms of a K definition and has no observer to evaluate a function in, so it refuses `observer`, `views`, `components`, `when` and `element` in `[observe]`, and a projection (P1) with `views` or an `observer` (admission stage `projection`, reason `unsupported-front-end`); identity contents and logs are sound at the K level by the argument that makes comparing an end's cells sound.
     A projection with views or an observer is resolved only by a front end that reads values, the krs front end (`krs kink`); a flow bound to a KRS definition is not refused.

  Why: P1 makes views and an observer parts of a projection, under which every command measures, so the refusal's scope must name projections as it names `[observe]`; the argument is unchanged, since a view or an observer is a function of values the K front end does not have.
  The last clause of the first paragraph no longer says "the end projection's argument", so that "projection" names only P1's object.
  [draft, 2026-11-19, not confirmed by Sebastien; moves into O1 with P1]
