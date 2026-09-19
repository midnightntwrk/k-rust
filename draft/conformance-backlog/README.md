# conformance-backlog: pending work behind every non-match conformance case

State: live. Ledger: `tickets.toml`.

`scripts/conformance/expectations.toml` gives every accepted non-`match` case one of two dispositions (`docs/compatibility.md` "Driver scope"):
a non-empty `exclusion` is a justification complete in the tracked repository;
an empty `exclusion` with a measured `reason` is pending work.
This ledger indexes the pending work.
Ticket identifiers stay here; the tracked files never name them.

`scripts/conformance-ratchet.sh --audit --log <log>` reads `tickets.toml` by default when it exists and exits 3 when a non-excluded case whose latest verdict is not `match` has no open case-owning ticket.
It also lists case-owning open tickets whose cases all match, which is the signal to close them, and lists evidence-only tickets separately.

Each `[[ticket]]` carries `id`, `title`, `state` (`open` or `closed`), `cases` (expectation case names), `measured` (the run that shows the current failure), `work` (what must change for the cases to match), and `elsewhere` (the older draft/ ledgers that already describe the same work, so that nothing is duplicated). `[[decision]]` rows in the same ledger centralize owner choices and constrain implementation. There are currently no open owner decisions. A choice whose correct answer depends on an investigation or benchmark is recorded as a decided selection rule, not as a question for an implementation worker to guess or escalate prematurely.
A ticket may group cases that share one cause. `case_role = "owner"` is the default and means the ticket owns those pending verdicts; `case_role = "evidence"` retains historical provenance for regression or product work that blocks no current case. Evidence-only tickets neither satisfy pending-case ownership nor appear in the all-cases-match closure signal.
A worked ticket also carries `resolution` (the decision and why, dated) and, when closed, `closed` (date, commit, and the shared-log sequence that justifies it); its long-form investigation is `workers/<id>.md` (sections: measured failure, cause, decision, work items as TOML, acceptance, and question disposition), written to the brief in `worker-brief.md`. Historical worker questions are not authority: each must say whether it was decided, superseded, split into another ticket, moved to a follow-up, or left as an evidence-gated implementation selection.
Two fields track how far a ticket has been taken, because the audit's `open`/`closed` state cannot say it: `worker` names the long-form investigation, and `investigation = "needed"` marks a ticket that has been recorded from a measurement but not yet investigated.
A ticket with `investigation = "needed"` and an empty `worker` must be fleshed out by an investigator before any implementation agent is given it; a ticket whose `worker` is set has a plan and goes straight to implementation.
Inside a worker file every `[[work_item]]` carries `state` (`open`, `partial`, `merged`, `done`, or `superseded`) and, when it is not open, `state_note` with the commit or the reason, so that an implementation agent reading only the worker file cannot redo merged work; the ticket's `work` field remains the prose summary.
`[[driver_followup]]` rows (`id`, `title`, `state`, `found`, `work`, `elsewhere`) record conformance-driver defects that are not tied to a pending case; the audit ignores them.
Seeded 2026-09-18 from ratchet sequence 4 (`target/conformance/ratchet.toml`, label `int`, HEAD `9c1a64d`) and four read-only searches of `draft/` recorded in `/tmp/nonmatch/coverage.md`.

## 2026-09-18: first pass over CB-01 to CB-08 (main af9481c)

Every ticket was reproduced with the driver on its own cases into the shared log (`target/conformance/ratchet.toml` sequences 5 to 12, labels `cb-07`, `cb-06`, `cb-05`, `cb-03`, `cb-02`, `cb-01`, `cb-04`, `cb-08`), then investigated by one sub-agent per ticket or pair (`workers/CB-0N.md`).
Nothing was pushed or merged; the branches below sit in `~/worktrees/cb-07` (`fix/cb-07-search-flag`) and `~/worktrees/cb-04` (`fix/cb-04-io-exclusion`, then `fix/cb-06-float-llvm-spelling`).

- CB-07 closed: driver defect fixed inline (`c153212`, one search mode per recipe plus the probe `conformance_driver_gives_a_search_recipe_exactly_one_search_flag`), floor raised to match/search (`cde0c35`); sequences 13 and 15 record match.
- CB-04 closed: step-level `llvm-only` exclusions for io.imp, locals.imp, sum-io.imp (`6e77386`); sequence 14 records the run as excluded, floor unchanged. Reversal (console IO as product) is the owner's decision; cost recorded in the ticket.
- CB-06 closed: case-level `llvm-only` exclusion (`a0ec49a`); sequence 16 records it. The ticket's premise was wrong: the Haskell oracle and the K frontend printer both spell the token `NaNp24x8`; only the LLVM runtime prints `NaNf`. A host-UID run should confirm the excluded mismatch.
- CB-05 closed without a commit: the case matches (sequence 7); the driver weakness moved to DF-03.
- CB-03 stays open, fleshed out: not a port regression but a driver recipe defect (the wrapped spec's bare `requires` line is blanked by Markdown extraction) plus a port gap (spec-required prepared sources are never re-read); the match floor came from a manual two-stage recipe, not from the driver. Four work items, hours to days, sandbox-runnable.
- CB-01 and CB-02 stay open, fleshed out as Bison-programme work: the port's generator already emits byte-identical parsers for all three fixtures; missing are the `--bison-parser-library` link flag, a `kast --gen-parser` entry point, and driver consumers (about a day each side). The contract prose in `docs/compatibility.md` and `README.md` still declares Bison generation out of scope and contradicts the port, the manifest and the expectations; owner to reconcile.
- CB-08 stays open, re-characterised: not throughput but super-exponential branching on ground programs. The frontend emits anywhere-ruled productions and overloaded list constructors without `constructor{}()`, the port loads them as total functions, a ground heating match is deferred as indeterminate instead of failing, and the rewriter narrows; collatz.simple explodes at step 7 (sequence 12 measures the 300 s timeouts; bounded runs in `workers/CB-08.md`). Work: rigid anywhere heads and a constructor-likeness gate in the backend (days each), then re-measure; the per-krun recompile (about 3 s of a shared 300 s budget for 28 to 50 programs) is a second item. Worktree `~/worktrees/cb-08` (branch `fix/cb-08-tutorial-throughput`) holds only the measure build, no commits.
- Driver follow-ups DF-01 (a swept work tree measured as skipped-with-reason and ranked as an improvement; eight bogus runs were scrubbed from the log by hand) and DF-02 (nested kompiled directories not cleaned between runs; one bogus run scrubbed) were found by the session itself.

Gates for each commit: `cargo test -p k-rust --test conformance_ratchet --test differential_manifest --no-default-features --features cli --locked` and `taplo lint scripts/conformance/expectations.toml`, run in the worktree with its own `CARGO_TARGET_DIR`.
Audit after the ledger update: 0 pending cases without an open ticket, no open ticket whose cases all match.

Merged to `main` on request: `ddb1b54` (CB-07), `33f51a2` (CB-04), `aa432de` (CB-06); gates and audit re-run on the merged `main`. Not pushed.

## 2026-09-18: implementation pass over CB-01, CB-02, CB-03, CB-08 and DF-01 to DF-03

Sequential Sol workers used one branch per coherent work area.

- DF-01 to DF-03 closed on `fix/conformance-driver-integrity` at `de1be303`: the driver validates and refreshes swept work trees, removes nested generated definitions before recipe expansion, classifies harness failure as `reference-error`, separates crashed reference reruns from stale oracles, and bounds reference RTS parallelism.
- CB-03 closed on `fix/cb-03-kprove-driver` at `ae9ba3b`: the real two-stage proof recipe replaces the generated Markdown wrapper, prepared sources are revalidated without duplicate lowering, and the final 42-case cohort has 38 matches, two existing unsupported cases, two existing excluded mismatches, and no regression.
- CB-01 and CB-02 closed on `fix/cb-01-02-bison-consumers` at `fa188be`: shared-library and standalone parser consumers use the external Bison/Flex/C toolchain; private ratchet sequence 1 records `match/bison-parser` for all three cases with byte-identical stdout.
- CB-08 remains open after the backend tranche on `fix/cb-08-ground-rewrite` at `7153d36`: SIMPLE untyped and KOOL untyped now complete all driven steps inside 300 seconds without branching, OOM, or SMT queries.
  The measured cases expose unsupported `IO.write`, nine typed-instantiation failures, two stale search oracles, and one 108-second factorial execution; five cases remain unmeasured.
  Floors were not lowered, and only the two measured expectation reasons changed.

Each branch passed its focused regressions and applicable repository gates.
The CB-08 branch additionally passed the full `k-rust` suite and backend measure ratchets.

Merged to `main` on request: `1973e38` (DF-01 to DF-03), `0121400` (CB-03), `3468254` (CB-01 and CB-02), and `88035ed` (CB-08, including the formatter-only amendment).
Nothing was pushed.
Combined main validation passed Python compilation, TOML lint, formatting, the 55 focused conformance/manifest tests, and the complete `k-rust` plus `k-rust-backend` suites.
Shared ratchet sequence 17 (`merged-conformance-backlog`) records match/bison-parser for CB-01 and both CB-02 cases and match/kprove for CB-03; the final audit reports zero non-excluded cases below floor and zero pending cases without an open ticket.

## 2026-09-18: second pass, the CB-08 residue (main 88035ed)

The seven language-tutorial cases were re-measured on `main` as shared sequence 18 (label `cb-08-main`, 833 s at `--jobs 2`; `target/conformance/runs/18-cb-08-main/`), then six Fable investigators fleshed out one ticket each from that run (`workers/CB-09.md` to `workers/CB-14.md`, brief in `worker-brief-round2.md`).
Nothing was fixed; nothing was pushed or merged.
The only tracked change is `fc110b9` on `fix/cb-08-remeasure` (worktree `~/worktrees/cb-08-remeasure`): the seven expectation reasons rewritten from sequence 18, floors unchanged, gates passed (39 conformance_ratchet and 16 differential_manifest tests, taplo).

- CB-08 closed as split: the titled budget failure is gone for six of the seven cases (no OOM, no branch explosion); the residue is CB-09 to CB-14 below.
- CB-09 (IO.write, 98 of 104 plain executions in four cases): owner's decision between step-level `llvm-only` exclusions (hours, masks the whole executing corpus), a backend IO evaluator (3 to 4 weeks, contract amendment), and the recommended driver-side comparison C9 that runs the recipe under `--io off` and byte-compares the stdout stream cell's `#buffer` with the `.out` (days; sound because the definition's own stream rules compute the bytes and the hook only transports them). No exclusion recorded.
- CB-10 (14 thread-program halts in the two SIMPLE executing cases): the anywhere-headed `_[_]` heating rule is deferred through `match_differing_injections` and the cell-map AC solver when two or more `<thread>` cells exist; a 25-line K fixture reproduces it. Backend fix, hours plus days.
- CB-11 (residual `isKResult` constraints on ground overloaded lists: three search results and, per CB-12, stuck remainder leaves on plain executions): the owise predicate is never tried because the KResult-versus-Exps injection pair is deferred for the anywhere head; the CB-08 rigid-head rule is gated on rewrite mode only. Backend fix, days; the driver's search translation is correct (closes CB-08-5).
- CB-12 (budget and throughput): each krun recompiles the definition (2.2 to 4.5 s, 77 to 131 s per case); factorial.kool's 43 ms/step is quadratic re-simplification of unchanged frames because overloaded and anywhere applications never count as `evaluated`. Port work: `krust krun --definition <kompiled dir>` with a run sidecar, driver reuse, simplifier counters and the `evaluated` fix. The measure build is `/tmp/cb-12-target/release/krust`; `~/worktrees/cb-12` (branch `probe/cb-12-throughput`) holds two uncommitted exploratory patches in `rewrite.rs` and `simplify.rs`, to be discarded.
- CB-13 (both static type checkers print `\bottom`, 65 steps, 29 of them hidden as completion-only matches): a simplifier unsoundness, `collect_constructor_exclusions` treats a ground `<task>` cell as excluding its sort's only constructor head, so SET.concat's pairwise-distinctness obligation refutes the step. W1 (hours) fixes the unsoundness; W2 (days) decides ground inequality of anywhere-injective heads. The cheapest genuine fix of this round.
- CB-14 (FUN ackermann.fun killed at 289.5 s): not throughput. `krust krun` expands program macros in the syntax module's scope, so FUN-UNTYPED-MACROS macros (27 of 50 programs) survive as non-constructor heads and every rule narrows against them; with that patched away the run still branches on the CB-11 mechanism. CLI fix plus the shared backend fix, days each.
- Driver follow-ups: DF-04 (completion-only `--output none` steps record match for `\bottom`) was found here and is now closed, merged at `8f34df5` with CB-09-W1. DF-05 is closed: the driver no longer sends its default `GHCRTS=-N1` through `krun --pattern` to non-threaded `kore-match-disjunction`, and host sequence 20 confirmed all 39 formerly blocked pattern oracles.

Shared mechanism: CB-10, CB-11, CB-13-W2 and CB-14-3 all stem from overloaded and anywhere-ruled productions arriving without `constructor{}()`; the fix must be one "concrete after normalisation" notion in `term.rs` (the CB-08-2 boundary) consumed by rewrite matching, injection matching, equation evaluation and predicate truth, not four predicates.
Owner decisions, 2026-09-18:

- CB-09 retains C9 as immediate and independent evidence; CB-15 makes committed-trace console IO a product feature, beginning with captured batch output and adding live delivery only after branch-local effect ownership is pinned.
- DF-04 must stop recording the 29 completion-only `\bottom` results as matches immediately; the measured expectation remains at the case's existing `kompile` floor while the semantic defect is fixed.
- CB-10, CB-11, CB-13-W2, and CB-14-3 must use one concrete-after-normalisation notion across rewrite matching, equation matching, sort membership, and predicate truth; `docs/compatibility.md` must state that common boundary.
- CB-12 may temporarily set `budget = 600` for the two KOOL execution cases, with an inline removal condition tied to the compiled-definition reuse measurement.
- CB-16 must make every ordinary `kcompile` output runnable without `--for-running`; it must inventory consumers and measure/select the representation before deciding JSON versus an existing binary serializer or placing metadata in `krust.json` versus consumer-native files. The CLI/library is the compatibility boundary, not a frozen internal directory layout.

Implementation progress, 2026-09-18:

- CB-09-W1/W2 and DF-04 merged at `8f34df5` (`0ef1de3`): C9 structurally compares one unconstrained buffered stdout leaf, completion-only `\bottom` is no longer a match, and the accepted floors are unchanged. Private `df-04-bottom` sequence 1 measured all 29 KOOL typed-static false matches as `krust-error/krun`; the partial C9 run removed SIMPLE's `IO.write` halts and exposed CB-11 residual leaves plus CB-12 budget exhaustion.
- CB-13-W1 merged at `22d113e` (`951ecb0`): a ground or partially instantiated constructor value no longer excludes its entire constructor family. The reduced cell-set fixture retains the inequality pending W2 instead of collapsing to bottom.
- The shared CB-11-1/CB-13-W2/CB-14-3 normalized-ground tranche merged at `5e1c373` (`82c440d`): one `concrete_after_normalization` notion now governs rewrite instantiation, overload-aware equation matching, and normalized structural inequality. SIMPLE `div-nondet.simple` has exactly its three results with no residual `isKResult`; FUN `factorial.fun` has one result and no branching; typed-static programs advance past the former bottom.
- The shared tranche exposed a distinct SIMPLE typed-static residue: unbounded `collatz.simple` reaches depth 3 and reports instantiation failure for rule `cf6aaec...`, missing `X:Id` and `T:Type`. This is not the CB-13 bottom mechanism or CB-10's collection-AC thread rule and needs a separate investigation before CB-13 can close.
- CB-15 and CB-16 were fleshed out after the owner review: committed-trace console IO is split from C9, and unconditional runnable artifacts are split from CB-12 throughput without prematurely choosing their internal layout.
Historical hygiene note: an earlier session reported an untracked `kore-match-disjunction.tar.gz` in the SIMPLE typed-static reference directory. It is no longer present as of the 2026-09-19 decision audit; this documentation pass does not attribute or perform its removal.
Audit after the ledger update: 0 pending cases without an open ticket, no open ticket whose cases all match, the three below-floor cases all excluded (pre-existing).

## 2026-09-18: state check and re-measurement after the three implementation tranches (main e4769a1)

This pass measured nothing new about mechanisms; it verified that the ledger describes the work that is actually left, and produced the first shared measurement of `main` since the tranches landed.
Sequences 18 and 20 both predate `8f34df5`, `22d113e` and `5e1c373`, so every `measured` field and expectation reason was written against superseded behaviour.

Shared sequence 21 (`target/conformance/runs/21-post-tranche-main/`, label `post-tranche-main`, all seven pending cases, 1291 s at `--jobs 2`, peak RSS 963 MiB, driver `30919e54`, `target/release/krust` rebuilt from `e4769a1`): 0 regressions, 0 cases below floor, 0 improvements in rank, two driver deltas where the typed-static cases move from `mismatch` to `krust-error` because DF-04 no longer accepts a completion-only `\bottom`.
Rank is unchanged everywhere, but 60 steps that did not match in sequence 18 now match.

What the tranches bought, measured:

- `IO.write` no longer halts anything. 51 executions match through the C9 stdout-buffer comparison (18 SIMPLE untyped, 3 SIMPLE typed-dynamic, 14 KOOL untyped, 16 KOOL typed-dynamic) and no step of any case reaches the hook. CB-09's own work is complete.
- CB-11 is confirmed by the driver, not only by fixtures: `div-nondet.simple` and `exceptions_07.simple` (SIMPLE untyped) and `div-nondet.simple` (typed-dynamic) match through the search disjunct multiset, with no residual `isKResult` and no stuck remainder leaf.
- CB-13 is closed. Neither type checker prints `\bottom` any more; SIMPLE typed-static runs its whole corpus in 90.4 s and KOOL typed-static in 131.1 s.
- CB-12's sequence-18 outlier, `factorial.kool` at 112.8 s, now matches inside the budget.

What replaced them:

- CB-17 (new) is now the only failure of both typed-static cases, one rule each: SIMPLE on `cf6aaec3` missing `Rule#VarX:Id` and `Rule#VarT:Type` at depths 2 to 114 (35 programs), KOOL on `d056a9d1` missing `Rule#VarE`, `Rule#VarT` and `Rule#VarTs` at depth 3 or 4 (30 programs).
- CB-19 (new) is `matrix`: `matrix.simple` exits 0 in 3.2 s printing `\bottom` in SIMPLE untyped, and the same source is killed at 233.6 s, 424.9 s and 378.7 s in the three other executing cases, exhausting each budget and leaving 21, 13 and 12 steps unmeasured. With FUN's `ackermann.fun` (289.6 s, 49 steps skipped), four cases now lose their corpus to a single outlier program rather than to many slow ones.
- CB-10 and CB-14 are unchanged: nine SIMPLE untyped thread programs still halt on `c892af32`, and `ackermann.fun` is still killed because CB-14-1 and CB-14-2 are unstarted.

Ledger hygiene done in this pass:

- DF-04 was `state = "open"` in the ledger while `README` line 84 and CB-13's `work` recorded it merged at `8f34df5`; it is closed with its evidence, and the contradicting round-two bullet now records the closure in place.
- Every `[[work_item]]` in the eight active worker files carries `state` (`open`, `partial`, `merged`, `done`, `superseded`) with `state_note` naming the commit, and each stale worker file's header says what merged and that its prose predates it. CB-11-3 is now superseded: its completed half is DF-05 and its remaining driver metadata work is DF-08.
- Tickets now carry `worker` and, when uninvestigated, `investigation = "needed"`, because the audit's `open`/`closed` cannot express it. CB-17, CB-18 and CB-19 are the three tickets that need an investigator before any implementation agent is given them.
- CB-18 (the `--pattern` hang found as CB-09 open question 3) was confirmed on current main: `krun … tests/hello-world.kool --io off --depth 0 --pattern '<k> .K </k>'` does not return within 120 s, and neither do `--depth 5` or `--depth 400`, while the identical invocations without `--pattern` return in 3 to 4 s.
- The seven expectation reasons were rewritten from sequence 21 and merged locally as `8d8eb32` (`4be78bf`); floors, stages and the two 600 s ceilings are unchanged. The obsolete `fc110b9` on `fix/cb-08-remeasure` is superseded and was not merged.
- Historical CB-12 handoff: the two exploratory probes were reported saved to `/tmp/cb-12-exploratory-probe-20260918.patch` and stashed in the agent worktree. At the 2026-09-19 ledger check the patch was absent, the agent-1 worktree was inaccessible from this UID, and Git marked its registration prunable. Do not run `git worktree prune` here; a session with that agent identity must decide its cleanup.

Gates: `cargo test -p k-rust --test conformance_ratchet --test differential_manifest --no-default-features --features cli --locked` passes (40 and 16 tests), `taplo lint scripts/conformance/expectations.toml` passes, and the audit reports 7 pending cases all measured at sequence 21, 0 pending without an open ticket, no open ticket whose cases all match, and 3 below-floor cases all excluded (pre-existing).

Superseded owner list: the reported archive is no longer present; later sequences replaced the 600-second ceilings with D-04's measured budgets; D-06 through D-11 now decide the oracle annotation, collection-AC scope, macro expansion layer, surviving macro heads, concrete instantiation classification, and console transcript policy.

## 2026-09-18: SIMPLE untyped and typed-dynamic receive the temporary 600 s ceiling (`0bcb7b3`, branch `chore/simple-budget-ceilings`)

Owner decision on the question left open above: the two SIMPLE cases get the same temporary correctness ceiling as the two KOOL cases (`e4769a1`), for the same reason and with the same removal condition (after CB-16 compiled-definition reuse is measured).
The justifying measurement is sequence 21 (`target/conformance/runs/21-post-tranche-main/`): SIMPLE untyped reached `seconds = 300.0` with 279.9 s of krust time over its 32 steps and threads_12 was the step killed by budget exhaustion after 3.0 s; SIMPLE typed-dynamic was killed on matrix.simple at 233.6 s and left 21 steps unmeasured (CB-19).
Only `budget = 600` and the two reasons changed; floors, stages and exclusions are unchanged, so no ticket state moves.
No new run was taken; the next shared sequence measures both cases under the ceiling.

Gates: `cargo test -p k-rust --test conformance_ratchet --test differential_manifest --no-default-features --features cli --locked` passes (40 and 16 tests) and `taplo lint scripts/conformance/expectations.toml` passes.

## 2026-09-18: sequence 22, the first measurement under the SIMPLE ceilings (branch `chore/simple-budget-ceilings`)

Shared sequence 22 (`target/conformance/runs/22-simple-ceiling-600/`, label `simple-ceiling-600`, the two SIMPLE cases, 600.2 s at `--jobs 2`, peak RSS 870 MiB, driver `30919e54`, krust rebuilt from `0bcb7b3`): 0 regressions, 0 below floor, 0 rank changes, 0 oracle changes.

- SIMPLE untyped: the whole corpus is measured for the first time, 32 steps in 304.4 s. Same 21 matches as sequence 21; threads_12, which the 300 s budget had killed, halts on rule c892af32 like the other nine thread programs (CB-10). `matrix.simple` still prints `\bottom` in 3.2 s (CB-19). `sortings.simple` matches but costs 155.8 s, half the case.
- SIMPLE typed-dynamic: `matrix.simple` terminates and matches in 418.3 s, so the sequence-21 reading that it does not terminate there was a budget artifact; that case's matrix failure is CB-12 throughput, not CB-19. The budget then dies on `sortings.simple` (killed at 115.0 s) and 20 steps stay unmeasured. The corpus needs roughly 800 s at current throughput; 600 s does not complete it.
- CB-19's `measured`/`work` were updated with this split. The cheapest next probe is an unbudgeted run of `matrix.kool` in KOOL untyped to learn whether the 424.9 s kill is the same slowness.

Both expectation reasons were rewritten from sequence 22; floors, stages, exclusions and the ceilings are unchanged. Gates: ratchet (40) and manifest (16) tests pass, `taplo lint` passes, audit: 0 pending without an open ticket, no open ticket whose cases all match.

## 2026-09-19: sequence 23, discovery budgets; both KOOL executing cases match (`4cabcc8`, branch `chore/simple-budget-ceilings`)

Owner decision: every case whose corpus was lost to one outlier got a 3600 s discovery budget for one run, to learn the real cost before shrinking. Shared sequence 23 (`target/conformance/runs/23-discovery-3600/`, label `discovery-3600`, SIMPLE typed-dynamic, KOOL untyped, KOOL typed-dynamic, FUN untyped, `--jobs 4`, 3600.3 s wall, peak RSS 4026 MiB, krust from `941dbfe`): 0 regressions, 2 improvements, 0 oracle changes.

- KOOL untyped and KOOL typed-dynamic match on every step (29 and 30) in 1244.9 s and 1361.2 s. `matrix.kool` was never divergent: 721.9 s and 764.0 s. Floors raised to `match`/`krun`; budgets set to 1800 s (measured cost with headroom, temporary until CB-16/CB-12).
- SIMPLE typed-dynamic completes in 815.1 s: 22 of 27 match; `matrix.simple` 470.5 s and `sortings.simple` 200.0 s both match. The five failures are the CB-10 thread halts. Budget set to 1200 s.
- FUN untyped: `ackermann.fun` killed at 3587.7 s, about 4 GiB RSS, 49 programs unmeasured. No budget helps while it runs first and the driver has no per-step ceiling; filed as DF-06 and the budget returns to the 300 s default. The mechanism is CB-14-1 (surviving FUN-UNTYPED-MACROS macros).
- CB-19 rescoped to the one real defect: `matrix.simple` printing `\bottom` in 3.2 s in SIMPLE untyped. The other three cases were removed from it; their matrix cost is CB-12.
- CB-12, CB-09 and CB-11 carry the sequence-23 measurement. CB-18 stays open although the audit now lists it under "open tickets whose cases all match": KOOL untyped's driven recipes never pass `--pattern`, so the match does not cover it.
- Timing note: at `--jobs 4` the same programs ran about 12 percent slower than at `--jobs 2` in sequence 22 (`matrix.simple` 470.5 s versus 418.3 s); the budgets include that.

Gates: ratchet (40) and manifest (16) tests pass, `taplo lint` on both TOML files passes, audit: 0 pending without an open ticket, CB-18 flagged as above.

Left for the owner: DF-06 (per-step ceiling) is the driver change that would let FUN's other 49 programs be measured before CB-14-1 lands; and whether to merge `chore/simple-budget-ceilings` (three commits: `0bcb7b3`, `941dbfe`, `4cabcc8`).

## 2026-09-19: DF-06 step budget implemented; FUN untyped measured in full (`e57e1c4`, branch `chore/simple-budget-ceilings`)

Owner decision: implement DF-06 rather than sweep FUN's programs by hand, because a manual sweep would have to reimplement the C9 stdout comparison and would not land in the ratchet log.
`scripts/conformance/run.py` gains an expectations `step_budget` that caps each krust program execution inside the case budget; a capped kill is `krust krun exceeded the step budget (N s)` with a `step_budget` field on the step, the programs behind it still run, and a step budget above its case budget is rejected. Reference re-runs and kompile steps keep the case budget. Regression test `conformance_driver_caps_each_program_by_the_step_budget_inside_the_case_budget`.

- Sequence 24 (`24-fun-step-budget`, budget 600 / step 60): ackermann.fun killed at 60 s as intended, but nine more programs hit 60 s and 35 were still unmeasured; ackermann was never the only outlier.
- Sequence 25 (`25-fun-step-budget-20`, budget 1200 / step 20, 751.5 s): all 51 steps measured. 15 programs match in 2.4 to 3.2 s; 35 are killed at 20 s; no mismatch. The initial attribution that every killed program used a construct FUN desugars was false: `list-length`, `list-max`, `nth`, and `factorial-and-list-max` use no FUN-UNTYPED-MACROS construct, while multi-clause functions and list patterns are core syntax. CB-14-1 owns the proven macro-scope cohort; CB-20 owns the macro-free cohort.
- Correction, same day: the 20 s step budget was chosen for wall time, not agreed, and by itself it only says "slower than 20 s". The 35 killed programs were therefore re-run with their recorded commands, eight in parallel, 1800 s hard kill each (`target/conformance/runs/25-fun-step-budget-20/sweep-1800/`, results.tsv and per-program logs). All 35 ran the full 1800 s with empty stdout: 31 at 1.2 to 2.3 GiB peak RSS, `nth` and `factorial-and-list-max` about 8.8 GiB, `list-length` 16 GiB, `list-max` 21 GiB. With `ackermann.fun` killed at 3587.7 s in sequence 23, the kills are non-termination with unbounded state growth, not slowness. FUN's budget is now step_budget 60 / budget 2700 from that measurement (`f006e6e`); the sequence-25 verdicts stand.
- No new ticket. DF-06 closed. FUN keeps its budgets until CB-14-1 lands and the case is re-measured.

Gates: ratchet (41) and manifest (16) tests pass, `cargo fmt --check` and `taplo lint` pass, audit unchanged (0 pending without a ticket, CB-18 flagged as before).

## 2026-09-19: round-three ledger correction and investigator handoff

This documentation-only pass checked the current ledger against sequences 20 through 25 and made no implementation or acceptance-floor change.

- Added `worker-brief-round3.md` for CB-17, CB-18, CB-19, and CB-20. It names `583a4ba`, the relevant sequences, DF-06, current budgets, and the fact that both KOOL executing cases match.
- Closed CB-09 because its IO.write failure class is gone; its overlapping cases remain covered by their actual open tickets. CB-11 remains narrowly open for its end-to-end CLI regression; CB-13-W3 is marked done because sequence 21 performed that remeasurement.
- Corrected CB-10's obsolete host-oracle and IO.write acceptance wording, CB-12's superseded 600-second ceilings, and CB-17's assertion that its Set-cell failure is a different path from CB-10. The Set/AC relationship is now an explicit hypothesis for the CB-17 investigator to prove or refute.
- Corrected CB-14's sequence-25 attribution. Four macro-free programs (`list-length`, `list-max`, `nth`, and `factorial-and-list-max`) invalidate the claim that every killed program uses a construct expanded by FUN-UNTYPED-MACROS. CB-20 now owns that uninvestigated cohort; CB-14 remains the wrong-macro-scope ticket.
- Added centralized `[[decision]]` rows to `tickets.toml`. The prior owner choices on C9, DF-04, normalized ground terms, temporary budgets, and runnable artifacts are recorded as decided. The later decision audit closes the reference-crash annotation policy and expresses Set-cell fixture scope as a conditional coverage rule rather than an unanswered owner choice.

## 2026-09-19: decision normalization

This documentation pass makes `tickets.toml` the unambiguous authority for policy while preserving worker investigations as evidence.

- D-06 keeps `reference-error` for a crashed or unavailable oracle and adds `oracle_confirmed = "not-run (reference crash)"`; a completed refutation alone uses `false`.
- D-07 requires CB-17 to establish the Set-cell mechanism before scope is assigned. A shared collection-AC invariant requires shared Map/Set contract and regression coverage; a distinct mechanism is split.
- D-08 selects the existing kast-domain Expander for `krun`, using the syntax module's parsed-term catalog and the main module's visible macro sentences.
- D-09 makes a surviving macro or alias head a pre-step CLI input error and retains a typed backend guard for direct callers.
- D-10 retains typed indeterminacy for genuinely unresolved concrete instantiation; CB-10 fixes the earlier missed impossible match rather than changing that public classification.
- D-11 makes captured batch console output explicit, starts with pre-buffered stdin, defers live interactive delivery until effect ownership is proved, and rejects search/RPC live IO until a separate structured transcript protocol exists. CB-15 is product work and blocks no current C9 conformance result.
- CB-16's representation and metadata choices are explicitly evidence-gated implementation selections, not owner questions.
- DF-07 now owns the only newly identified evidence gap: whether specific upstream-disabled typed-dynamic search recipes require `undriven-recipe` records or expose a driver translation defect.
- CB-11 and CB-15 are evidence-only tickets: the former closes when its CLI regression lands, while its crashed-oracle metadata remainder is DF-08; the latter is product work that never gates C9 verdicts.

All worker sections formerly titled "Open questions" now record dispositions or evidence-gated selections. No owner decision remains open; investigators may create a new decision row only when first-principles constraints and available evidence do not determine the answer.

## 2026-09-19: CB-10 collection-AC rewrite recovery (`2f02ecb`, `fix/cb-10-collection-ac`)

CB-10's semantic failure class is closed. Rewrite matching now decides normalized rewrite-rigid heads beneath widening injections in either orientation, and collection-AC candidates retry Rewrite matching before symbolic unification. Evaluate, Implies, declared function heads, and `unification.rs` keep their symbolic contracts. A dedicated MAP cell fixture covers one and two entries plus a positive literal-head selection; its measure regression records collection solving without symbolic unification or SMT. The source-driven `star-cell-heating` CLI fixture completes one-cell, immediate-spawn, and late-spawn programs, and its `kore/llvm` compile differential passes semantic, syntax, macro, and parsed-definition comparisons.

Private sequence 1 (`target/conformance/cb-10-collection-ac/runs/1-cb-10-collection-ac/`, label `cb-10-collection-ac`, 1200.2 s at `--jobs 2`, peak RSS 886 MiB) preserves both accepted floors and both temporary budgets. SIMPLE untyped records 24 matches: `threads_01`, `threads_02`, and `threads_04` newly match at search in 4.7, 6.2, and 107.9 s. `threads_05` consumes the remaining 207.1 s, six later thread recipes are budget-skipped, and `matrix.simple` remains CB-19's bottom result. SIMPLE typed-dynamic records 22 matches; `threads_05` consumes the remaining 493.5 s and the other four thread recipes are budget-skipped.

Focused invocations cover every killed or skipped thread recipe and cross every former instantiation depth. Untyped 05/06/09 complete bounded searches at depths 50/50/40, 07/10/11 complete fully, and 12 reaches depth 100; typed-dynamic 05 reaches depth 50, 07/10/11 complete fully, and 12 reaches depth 100. No run reports `Instantiation`. Untyped `threads_12` still exceeds 300 s without a depth bound. The cases therefore remain pending under CB-12 throughput (and SIMPLE untyped under CB-19), but not under CB-10; no floor or budget changed.

Review qualification: CB-12 owns the newly exposed thread costs as an unclassified throughput residue, not as an already-proven instance of its repeated-simplification mechanism. Its work now requires counters and state-growth evidence on `threads_04`, `threads_05`, and `threads_12`, with a split if that mechanism does not explain them.

## 2026-09-19: CB-17 investigated on `main` at `cd1c86e` (sequence 26, `workers/CB-17.md`)

Investigation only; no tracked file changed and no floor moved.

- Shared sequence 26 (`target/conformance/runs/26-cb-17-main/`, label `cb-17-main`, both typed-static cases, 300.2 s at `--jobs 2`, peak RSS 944 MiB, driver `04a8b9fc`, `target/release/krust` rebuilt from `cd1c86e`): the titled `Instantiation` halts are gone from every step. Both cases stay `krust-error` at the same rank: SIMPLE typed-static loses its corpus to a 287.7 s kill of `collatz.simple`, KOOL typed-static halts `cast-1.kool` and `cast-2.kool` with `Indeterminate(Match …f66a5e22…)` and loses the rest to a 250.1 s kill of `collatz.kool`.
- D-07 is decided as "shared mechanism": `2f02ecb` (CB-10) removed the Set-cell instantiation halts without any typed-static change, because the Set solver resolves candidates through the same `solve_term_pair`. The Set-multiplicity regression coverage D-07 then requires does not exist yet (CB-17-D).
- Three residual mechanisms were established by bounded probes and code reading (`workers/CB-17.md` M1 to M3): `--strategy any` keeps every collection candidate of the first applicable rule and explores every task interleaving (disjunct counts 2 to 12 between depths 10 and 60; a one-line probe in `~/worktrees/cb-17-probe` turns the killed `collatz.simple` into an 8.2 s run); a ground Set definedness predicate `\not(\equals(task, task))` is never decided because `predicate_truth` uses `constructor_like` instead of the D-03 boundary, so the `#Top` pattern answer prints as `\not(…)`; and KOOL's upcast and member-lookup rules bind a Map-cell key inside a Set-cell element, which the sequential collection-pair solver attempts before the key is bound. Five work items: CB-17-A (any-mode single application, both cases), CB-17-B (ground definedness at the D-03 boundary, SIMPLE), CB-17-C (dependency-ordered collection pairs, KOOL), CB-17-D (D-07 Set coverage), CB-17-E (re-measure and rewrite the two expectation reasons, which still describe sequence 21).
- Ledger: CB-17 now carries `worker = "workers/CB-17.md"` and no `investigation` flag; its `measured`, `work`, `resolution` and `elsewhere` were rewritten from sequence 26 and the probes.
- The KOOL trace's minimal fixture (`cb17k.k` and its programs and controls) is kept at `workers/CB-17-fixture/`; it reproduces the Map-pair-before-Set-pair halt and is the base of CB-17-C's regression.
- Left in place for the implementer: the probe worktree `~/worktrees/cb-17-probe` (branch `probe/cb-17-any-single-successor`, uncommitted, own `target/`, results in `probe-out/`); delete it when CB-17-A lands.

Gates: `taplo lint draft/conformance-backlog/tickets.toml` passes; audit: 5 pending cases all owned, 0 pending without an open ticket, CB-18 still flagged as before, 3 below-floor cases all excluded (pre-existing).

## 2026-09-19: CB-17 implemented and closed

CB-17-A through E are complete. Any-mode rewriting now chooses one deterministic collection-candidate group without dropping right-hand-side alternatives; normalized-ground Set definedness no longer leaves task inequalities on the path; deferred collection pairs retry to a fixed point and nested collection residuals return to the collection solver. Dedicated Set-cell backend and measure regressions cover the D-07 invariant, and the KOOL reproducer is promoted to the source-level `star-cell-map-nested-set` CLI and differential fixture.

Private closure run v3 (`target/conformance/cb-17-implementation-v3/`, 1500 s discovery ceilings, `--jobs 2`, 1437.3 s wall, 996 MiB peak RSS) matches all 67 driven steps: SIMPLE typed-static 36/36 in 915.7 s and KOOL typed-static 31/31 in 1437.2 s. The former KOOL witnesses `cast-1.kool` and `cast-2.kool` match in 13.5 s and 9.6 s. No `Instantiation`, `Indeterminate`, residual Set inequality, or budget kill remains. The floors rise to `match`/`krun`; temporary budgets are 1200 s for SIMPLE and 1800 s for KOOL. Remaining single-path costs (`sortings.simple` 490.4 s, `matrix.kool` 361.4 s, `sorting.kool` 686.9 s) belong to CB-12.

This is local ignored ratchet sequence 27 with a revision explicitly marked dirty, not a shared merged-main run, because it measured the uncommitted implementation. The final candidate-group preservation tweak was verified afterward by all 621 backend tests/ratchets and the two source-level CLI regressions. The disposable `~/worktrees/cb-17-probe` worktree was removed after CB-17-A landed.

Gates: ratchet (41), manifest (16), all backend tests (391 library, 217 integration, 13 measure ratchets), both focused CLI regressions, `cargo fmt --check`, `taplo lint`, and `git diff --check` pass. The audit reports 3 pending cases, 0 pending without an open ticket, and 0 non-excluded cases below floor; CB-18 remains the known evidence exception whose driven case already matches.

## 2026-09-19: CB-19 investigated (no implementation)

`workers/CB-19.md` on `main` at `90ca9d6`. The 3.2 s `\bottom` of `matrix.simple` in SIMPLE untyped is not a backend defect. A `--depth` bisection with the recorded command lands on step 50, K's own `STDIN-STREAM.stdinParseInt` rule: `matrix.simple.in` is `2  4 \t1\n5 7 8 27\n\n1 2 3\n`, the first `read()` consumes `2` and one delimiter, and under `--io off` the rule then applies `String2Int("")` to the buffer that starts with the second space. The pinned LLVM interpreter under `--io off` aborts at the same depth (`hook_STRING_string2base_long: Not a valid integer`, exit 134), the pinned Kore engine returns `\bottom` on a reduced fixture (`workers/CB-19-fixture/`; the SIMPLE definition itself is not Haskell-compilable because of its anywhere rules), and krust returns `\bottom`, which is Kore's `String2Int` contract plus "Trivial rule results". The checked-in output is reachable only under the recipe's default `--io on`, where the buffer grows one character at a time and `stdinTrim` skips the delimiter. It is the only one of the 26 regression-new `.in` files with a delimiter run; the typed-dynamic and KOOL matrix inputs are single-space separated.

Ticket rescoped to a driver gap plus an observability gap, with three work items: CB-19-A (krun reports a mid-run trivial/vacuous collapse on stderr with depth, rule, and refuted obligation), CB-19-B (C9 stdin precondition: such a step is `skipped-with-reason` under an `undriven-recipe` `step_exclusions` row, keyed on krust's diagnostic and the `.in` bytes), CB-19-C (fixture promotion and re-measurement). No new decision row; CB-15-5 (`--io on` stdin) is the reconsideration trigger. `tickets.toml` updated (`investigation = "done"`, `worker`, `measured`, `work`, `elsewhere`); no floor, budget, or expectations change. Gates: `taplo lint` on `tickets.toml` and on the work-item block pass; the audit is unchanged (3 pending cases, 0 without an open ticket).

## 2026-09-19: CB-18 investigated (no implementation)

`workers/CB-18.md` on `main` at `90ca9d6`, evidence under `workers/CB-18-evidence/` (`runs.toml` index). The `--pattern` hang is not in the pattern path and is not a defect: the recorded command blocks in the `--io off` read of standard input to end of file (`main.rs:2249-2262`, `read_stdin_for_stream`), which the pinned `krun` script performs the same way (`krun:553-558`); with a never-closing pipe both the `--pattern` and the plain invocation are killed at 60 s with no output, and so is the reference `krun`, while from `/dev/null` the `--pattern` run returns in 4.0 s at `--depth 0`, 5, 400 and unbounded, printing `\bottom`, and exits normally under gdb. The 2026-09-18 contrast between the two invocations (`README.md` entry above, "identical invocations without `--pattern` return in 3 to 4 s") is superseded: the code reads standard input regardless of `--pattern`, and the earlier no-pattern figures must have come from a closed standard input. The driver always passes `/dev/null` or the `.in` file, so no driven step can block.

The pattern path was compared against the reference (LLVM backend kompiled `--enable-search`, `krun --output kore`, host UID) on twelve probes of `hello-world.kool`, including the `<output> … #buffer(S:String) …</output>` pattern CB-09 first recorded as hanging: every probe agrees, `\bottom` for `<k> .K </k>` at every depth being correct because `kool-untyped.md:528` removes the finished thread. The Set-typed star-cell fixture `STAR-CELL-HEATING-SET` agrees the same way. The only differences are in the KORE projection (the reference prints the `_DotVar` rest-variable bindings that krust projects; its text output prints only the named variables) and in the string-literal escape of a newline (`\x0a` against `\n`), neither visible to the driven text comparison.

Ticket rescoped to a regression plus a docs and observability item, three work items: CB-18-A (CLI tests: `--pattern` under `--io off` with a closed stdin pipe completes; `STAR-CELL-HEATING-SET` patterns project as the recorded reference outputs), CB-18-B (`docs/testing.md` Harness recipes states the end-of-file read and the redirect rule; a stderr note only when standard input is a terminal; `--io` help says "to end of file"), CB-18-C (closure, audit, annotation of `workers/CB-09.md:66` and `:249`). Rejected: a timeout or pipe-skip on the stdin read, any change to the pattern path. No new decision row. `tickets.toml` updated (`investigation = "done"`, `worker`, retitled, `measured`, `work`, `resolution`, `elsewhere`); no floor, budget, or expectations change. Reference kompiled trees were scratch-only and deleted; nothing under the pinned checkout was modified. Gates: `taplo lint` on `tickets.toml` and on `workers/CB-18-evidence/runs.toml` pass; audit: 3 pending cases all owned, 0 pending without an open ticket, CB-18 listed under open tickets whose cases all match (the expected state until CB-18-C), 3 below-floor cases all excluded (pre-existing).

## 2026-09-19: CB-18 implemented and closed (`119c32e`, `f2b2f20`)

CB-18-A at `119c32e` pins that `--pattern` under `--io off` completes after a piped standard input closes and returns the `KK` binding, and that ground and named patterns on the Set-typed star-cell fixture project the recorded reference results for one and two cells, including the injected program at depth zero.
CB-18-B at `f2b2f20` states the end-of-file read in the `--io` help and harness recipes and emits a note before a terminal read; piped and file input remain silent.
The two stale CB-09 records now identify the open standard input as the source of the recorded kills.
No execution, expectation, floor, normalisation, exclusion, or differential-manifest entry changed.

Gates: both focused CLI regressions, all five `io_off` CLI tests, a pseudo-terminal smoke test of the terminal-only note, `cargo fmt --check`, `taplo lint` on `tickets.toml`, and `git diff --check` pass.
The audit reports 3 pending cases, 0 pending without an open ticket, and 0 open tickets whose cases all match; the 3 below-floor cases remain excluded.

## 2026-09-19: CB-19 implemented and closed (`0188e8a`, `086fd75`, `f280fc0`)

CB-19-A/C at `0188e8a` retain the innermost partial builtin application that becomes undefined, carry the applied rule and refuted obligation on trivial execution leaves, and report every dropped trivial or vacuous CLI leaf with its semantic depth while preserving `\bottom`, exit status, RPC and search behavior.
CB-19-A review completion at `f280fc0` carries the latest applied-rule identity on vacuous execution leaves and names the label, or unique ID fallback, in their CLI diagnostic; initial vacuity remains unattributed.
The reduced stdin delimiter fixture is promoted under `crates/k-rust/tests/fixtures/reference/execution/stdin-delimiter-run/`: a single delimiter completes with stdout buffer `241`, while a leading delimiter and a delimiter run return `\bottom` with `STDIN-STREAM.stdinParseInt` and `String2Int("")` in the diagnostic.

CB-19-B at `086fd75` makes C9 read the `#parseInput(_, D)` delimiter literal generated into `krust-kompiled/definition.kore` and recognize only a leading or adjacent delimiter together with krust's attributed `STDIN-STREAM` diagnostic.
That step becomes `skipped-with-reason` under the existing `undriven-recipe` doctrine; every other input-program `\bottom` remains a DF-04 error.
The C9 register, compatibility guide, category meaning and SIMPLE untyped `step_exclusions` row record the precondition and the CB-15-5 reconsideration trigger.

Private sequence 28 (`target/conformance/runs/28-cb-19-implementation-private/`, 600.2 s, `--jobs 1`, peak RSS 838 MiB) preserves the case floor and budget.
Of 32 steps, 24 match, `matrix.simple` is skipped with the C9 stdin precondition in 3.3 s, `threads_05` consumes the remaining 286.2 s, and `threads_06/07/09/10/11/12` are budget-skipped.
The post-closure audit lists the case under CB-12 and CB-16 only; CB-19 is closed with no backend semantic change, normalisation, floor or budget change.

## 2026-09-19: CB-14 main-module macro expansion implemented and closed (`ea60da8`)

CB-14-1 and CB-14-2 landed together at `ea60da8`.
`krust krun` now parses programs and configuration values with the selected parser module's production catalog while sourcing executable macro rules from the selected main module.
Macro templates are rebased into that catalog, private lexical tokens retain their explicit sorts, and application metadata remains strict.
Every CLI, backend, search, wire, and RPC execution boundary rejects a surviving macro- or alias-headed application with a typed error before simplification, matching, rewrite recovery, or a zero-bound return.
The existing `kast` and search-pattern macro scopes remain unchanged.

Review found no remaining actionable issue after coverage was added for private macro tokens, strict application metadata, raw aliases, nested constraint terms, state and path search, zero breadth/result bounds, and facade and RPC entry points.
The implementation passed all 391 backend library tests, all 218 backend integration tests, 15 macro-pass tests, focused CLI and facade regressions, formatting, and whitespace checks.
Focused release probes for `ackermann.fun`, `list-1.fun`, `tuple-1.fun`, `exceptions.fun`, and `factorial.fun` each produce one matching result with no disjunction, surviving macro head, or residual `isKResult` predicate; `ackermann.fun` completes in 5.0 seconds.

The private `cb-14-final` implementation-candidate run measures all 51 driven steps in 838.9 seconds with 2062 MiB peak RSS.
The kompile step and 38/50 programs match, compared with 15/50 programs in sequence 25.
Twelve programs reach the unchanged 60-second step budget, with no mismatch or new error class.
Eight formerly macro-using programs still diverge after their macro heads are erased, alongside the four existing macro-free witnesses.
That twelve-program post-expansion cohort transfers to CB-20.
The FUN case remains `krust-error` under CB-20, CB-12, and CB-16; its accepted floor, 2700-second case budget, and 60-second step budget do not change.

## 2026-09-19: CB-11 end-to-end search regression implemented and ticket closed (`77f4f02`)

CB-11-2 at `77f4f02` promotes the remaining contract into a source-level CLI regression under `crates/k-rust/tests/fixtures/reference/search/simple-print/`.
The reduced SIMPLE-shaped definition retains the strict overloaded `Exps`/`Vals` list, a `print` statement whose first argument is the non-value expression `choose`, two nondeterministic `choose` rewrites, and the stdout stream buffer.
The test invokes `krust krun --search-final --pattern '<output> ListItem(#ostream(1)) ListItem("off") ListItem(#buffer(S:String)) </output>'` without an explicit `--io` flag, so it also pins search's `--io off` default and surface-pattern disjunct printing.

The parsed result has exactly two disjuncts whose user binding multiset is `S = "1\n"` and `S = "2\n"`.
The structural assertion rejects a residual `isKResult` or `\not` constraint, an extra user binding, a duplicate `S` binding, and the former empty-output remainder branch.
The focused CLI test and formatting check pass; no expectation, floor, budget, exclusion, or conformance case ownership changes.
CB-11 is closed; DF-08 continues to own the independent crashed-oracle annotation.

## 2026-09-19: DF-08 oracle confirmation tri-state implemented

The conformance driver now records `oracle_confirmed = "not-run (reference crash)"` when a crash, timeout, or unavailable direct reference command prevents an oracle confirmation.
It retains the `reference-error` verdict, existing reason and stderr evidence, and the krust divergence.
Completed refutations record `false`, including a non-crashing filtered recipe whose pipeline exits nonzero, while successful reproductions record `true`.

`conformance_driver_distinguishes_reference_crashes_from_stale_oracles` covers the three states, direct and pipeline failure semantics, environmental unavailability, timeout, and diagnostic preservation.
The focused test passed under `with-z3-static-4.16.0`; formatting, Python compilation, and whitespace checks pass.
DF-08 is closed with D-06 implemented and documented in `docs/testing.md`.

## 2026-09-19: DF-07 typed-dynamic recipe enumeration closed

A fresh conformance driver work tree from pinned K revision `4a46d1231473b599c699160132fd6e76a5c46406` confirms that SIMPLE typed-dynamic's `krun` target lists every program, but `make -n all` emits none of the search-pattern recipes for `exceptions_07.simple` and `threads_01/02/04/06/09.simple`.
The same fresh tree emits the intended `--search --pattern` recipe when each of those six paths is requested as the exact make goal.

The Makefile declares those paths and `div-nondet.simple` as the seven targets of one pattern rule.
GNU Make 4.4.1 selects the seven-target pattern rule as one multi-target implicit-rule application: `div-nondet.simple` occurs first in the wildcard-sorted `TESTS` prerequisites, selects the rule, and causes the six peers to be marked `considered already`.
The recipe uses `$@` and updates only that selected target, so the omission is an upstream Makefile mistake rather than an intentional disable.

The conformance driver correctly translates the effective upstream `all` goal and must not invent extra exact-target executions.
The typed-dynamic expectation reason records the six targets as `undriven-recipe` evidence, and `workers/DF-07-recipe-enumeration.toml` preserves the fresh-copy marker plus every exact invocation.
No `step_exclusions` rows were added because the driver has no result steps to select; adding exclusions would mask a mismatch if a later upstream Makefile starts driving these targets.
DF-07 closes without a driver change, floor change, budget change, or remeasurement.

## 2026-09-19: CB-16 runnable artifacts implemented; CB-21 split

CB-16-1 through CB-16-6 landed at `8e7931d`.
Every ordinary Rust `kcompile` now publishes a versioned runnable artifact, `krun --definition` loads it without source loading or compiler transforms, and the conformance driver reuses one Rust artifact per case.
LLVM comparison output stays separate: only LLVM cases with `krun` recipes perform and record one additional Rust runtime compilation.
The macro fixture writes its artifact in 0.0517 s and loads it in a median 0.0238 s; SIMPLE untyped writes in 0.7100 s and reaches its current frontend error after artifact loading in a median 0.3123 s.

The SIMPLE untyped acceptance probe cannot complete CB-16-7 because every attempted program stops at `source production metadata #324 on a macro application has no equivalent in the caller catalog`.
The exact source-driven `collatz.simple` command fails with the identical diagnostic, so this is neither artifact corruption nor a source fallback defect.
CB-21 now owns that source-execution failure and must identify production 324, the affected macro application, and the mismatch between the parser-module source catalog and main-module caller catalog.
CB-14 remains closed while the relationship to its strict metadata rebasing is unverified, and CB-20 remains the independent FUN post-expansion timeout investigation.
CB-16 stays open only for the seven-case remeasurement and temporary-budget adjustment after CB-21; no floor or budget changes are justified by the interrupted probe.

## 2026-09-19: CB-21 and CB-16 closed

CB-21 closes at `b71227a` as a CB-14 follow-up port regression.
Executable applications now transition from the selected parser catalog into the main catalog before main-visible macro expansion, sort injection, and KORE conversion; only self-describing tokens may discard unavailable source production metadata, with parser-first and main-fallback lexical hooks.
The exact guarded SIMPLE source invocation, the source/artifact cross-catalog fixture, the complete CLI suite, and the final SIMPLE case all pass without the caller-catalog diagnostic.

The final CB-16 acceptance run on `main` at `b71227a` used the seven tutorial cases with `--jobs 2` and completed in 3220 s (`/tmp/k-rust-cb16-final/results.toml`, SHA-256 `969fcaf69b963bbff5f504ec974b435e60809cc279217fd412888e231a34846b`).
Every case records exactly one ordinary LLVM comparison compile and one successful Rust runtime compile.
All 219 executed program commands use `krun --definition krust-kompiled-runtime`; none repeats source loading or compiler transforms.
The existing driver regression retains the complementary compile-only and LLVM-only no-runtime-compile contract.

| case | result | case s | runtime compile s | largest program costs | budget |
|---|---|---:|---:|---|---:|
| SIMPLE untyped | CB-12 search ceiling | 600.0 | 3.9 | threads_05 350.6 s; threads_04 100.2 s | 600 retained |
| SIMPLE typed static | match | 878.6 | 2.3 | sortings 505.1 s; matrix 203.5 s | 1200 retained |
| SIMPLE typed dynamic | CB-12 search ceiling | 1200.1 | 4.2 | threads_05 940.7 s; matrix 107.2 s | 1200 retained |
| KOOL untyped | match | 543.6 | 6.0 | matrix 265.1 s; sorting 188.7 s | 1800 → 900 |
| KOOL typed dynamic | match | 626.7 | 6.7 | matrix 291.3 s; sorting 215.2 s | 1800 → 900 |
| KOOL typed static | match | 1419.6 | 4.1 | sorting 725.8 s; matrix 374.8 s | 1800 retained |
| FUN untyped | 38 matches, 12 CB-20 step timeouts | 749.4 | 2.7 | each timeout 60.1 s | 2700 → 1200; step 60 retained |

Cheap-program medians are 0.3 to 1.5 s, compared with the superseded 2.2 to 4.5 s source-recompilation floor; these whole-program figures remain upper bounds on loading, parsing, and execution, while the isolated macro-fixture artifact-load median is 0.0238 s.
The long programs in the table are semantic execution or search costs and remain under CB-12 or CB-20.
CB-16 closes with all seven work items complete and no accepted floor change.

Gates: `taplo lint` passes for the expectations and ticket ledgers, `git diff --check` passes, and the conformance audit reports three pending cases, all owned by CB-12 or CB-20, with no open ticket whose cases all match and no non-excluded case below its accepted floor.
