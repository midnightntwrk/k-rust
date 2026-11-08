# Decision register (settled — do not re-litigate)

This register collects kink's settled design decisions as they are recorded, starting with M1, each stated as a rule an implementer can follow.
Decisions settled before the register began stay stated where they apply, in kink's READMEs and its trust document ([`trust.md`](trust.md)).
Each entry states its reasons from first principles and summarizes the measured evidence it rests on, so the entry is complete without any other record.
**This register is the normative statement.**
A proposal to change an entry must answer the entry's reasons and meet its reopening condition; a proposal that only restates a rejected alternative is not a reason to reopen it.

## M. Mutation input

- **M1 — Mutations of a KRS specification are K patches anchored by KRS item names, not Rust edits.**
  A mutation kink stores and runs is a set of text edits of the K definition KRS emits (`krs emit-k`'s `definition.k`), each addressed to one rule sentence by its label.
  Every rule sentence KRS emits carries a label that names its KRS item: the label its author wrote, or one derived from the item's stable identity, so it does not change when the sentence's text changes.
  The equations of an if/else or match body are named by their branch's position: adding a branch at the end keeps every name, but inserting or removing a branch renames the branches after it, and a patch anchored to one of those then resolves against whichever branch bears its name now and is refused unless its text occurs there; a branch whose mutations should survive such edits carries `#[k::label(..)]`.
  On every run each patch is resolved against the current K, all or nothing: an edit whose anchored sentence is gone, or whose text no longer occurs in it exactly, refuses the mutation and names the anchor.
  A Rust edit is not a mutation format, and no Rust-to-K translation step is built.
  [Sebastien, 2026-11-03]
  1. *What kink judges is a patch either way.*
     Every route ends at the same object, a kink-patch `Patch` over the K definition's sentences, and kink's verdicts, its soundness argument and its caches are about that patch and the definition it edits.
     The format is therefore only a question of what the author writes and how it becomes the patch.
  2. *Staleness is exact, with no cache argument.*
     A K patch states the text it replaces in the definition it applies to.
     After any edit of the specification the K is emitted again and every patch either still matches its anchor exactly, and is then exactly the stated edit of the current definition, or is refused.
     Freshness is a text comparison against the current definition; nothing needs to be argued about which parts of the specification an edit could affect.
  3. *No build per mutant or per specification edit.*
     kink loads the edited K in process; a Rust edit becomes a patch through today's build of the whole specification (a cargo build of KRS's collector, a run of it that re-parses the source, lowering and rendering of the whole definition, and a K diff).
     Measured on Foldiboy's SM83 specification at k-rust `40a359bcd` (the desktop host at its ordinary load average of 27-172, warm build directory), that build costs 17-61 s per mutant (median 31.6 s), against kink's own median of 0.92 s per mutant (mean 2.26 s; Foldiboy's 79 mutations over 17 programs, fresh cache).
     Without cargo at all, lowering and rendering the whole definition alone took 2-14 s per mutant.
     Parallel builds need one warm build directory per worker, about 2.3 GB each, because a copy at another path builds cold (about 132 s).
  4. *Rust-derived patches cannot be kept fresh cheaply or safely.*
     The K a Rust edit gives depends on every input of the lowering, not only on the edited item: after a specification edit adds a new use of a mutated constant, the patch derived earlier misses that use, and its text may still match.
     Rebuilding every Rust-derived mutation after every specification edit costs about 40 minutes for Foldiboy's 79 mutations; rejected.
     Rebuilding only the mutations whose lowering dependencies changed needs a dependency analysis covering every input of the lowering, whose gaps are silent: nothing compares the cached patch with what a build would give now; rejected as a staleness risk.
  5. *Writing K is as accurate.*
     In an experiment, one agent per arm expressed the same ten SM83 misunderstandings, given in prose, as K patches over the emitted K and as Rust edits, and each result was compared with a reference mutant built from a hand-written Rust edit.
     The K patches were as accurate as the Rust edits on the first attempt (every edit applied; 9 or 10 of 10 identical to the reference, the remaining one an equivalent form), including a constant used in five places and the edits spanning two sentences.
     The Rust arm used the fewest tokens and was the fastest (77k tokens and 61 s, against 115k and 121 s for plain K and 116k and 92 s for annotated K), but each of its edits still needs reason 3's build before kink can run it.
     The experiment's limits: one agent per arm, one model, a 993-line K definition, and misunderstandings given to the agents rather than invented by them.
     On that evidence a Rust-to-K translation step buys no accuracy, so it is not built.
     The agent whose comments named each sentence's Rust item, file and lines needed half the tool calls; it reported using them to map a sentence to its item, find shared constants and tell explicit `requires` clauses from generated ones, which needs the item and file, so the emitted K should carry that mapping.

  Accepted cost: a misunderstanding that spans several sentences (a constant used in several places, a bit template expanded into several conjuncts) is written out in K, every affected sentence edited.
  A patch that still matches after a specification edit is a sound mutant of the current definition, but it may express a different misunderstanding than its author meant (the new use of a constant above); keeping a mutation meaningful is the author's judgement, as keeping a test meaningful is.
  A K edit can also give a definition no KRS source emits, so the front end must refuse an edit that changes only nodes KRS inserted on its own (definedness tests, key guards, implicit frames, generated binders), and one whose derived nodes are not what KRS derives from the edited authored node.
  Text that renders authored syntax stays editable: a `k::bits!` template's fixed-bit tests and field reads, an if/else chain's repeated negated conditions, a `..` frame the author wrote.
  A mutant then stays a misunderstanding an author could have written.
  Rejected: Rust edits built through `krs emit-k` (above); Rust edits re-collected in process (they still lower the whole definition, 2-14 s per mutant, and keep reason 4's staleness); edits of KRS's intermediate representation (it has no authored text form other than its K rendering, so an edit of it is a K patch or a Rust re-collection in another form).
  Reopen the canonical format only on a Rust route measured close to kink's own cost per mutant, such as lowering a single item in process or compiling all mutants in one build, that keeps staleness an exact comparison.
  Reopen the no-translation clause alone, leaving K patches the canonical format, on new accuracy evidence: agents writing K patches measurably less accurately than Rust edits on a larger specification justify a one-off translation of a Rust edit into a K patch, which is then stored and checked as any other K patch.

## U. User surface

- **U1 — kink has one user tool; kink-corpus's manifest, binary and summary are kink's harness.**
  A user describes a corpus in kink-flow's `FLOW.toml` (directly, or through the krs front end, `krs kink`, for a KRS package) and reads kink-flow's statuses.
  A capability of kink-corpus's harness manifest reaches users only as a form of `FLOW.toml` stated in the specification's own terms: its declared inputs, its cell names, K text edits of it.
  kink-corpus stays the admission-and-input library both front ends build on, and its binary, manifest, store and summary stay kink's harness, used by kink's tests and its maintainers (`crates/kink-corpus/README.md` maps each harness capability to the user tool's form or states why users have none).
  [settled from first principles, 2026-11-04]
  1. *A second user format adds no verdict.*
     Every user-facing verdict, cache and soundness argument is kink-flow's: its kill definition, its outcome cache and `--verify`, its documents.
     A second manifest a user could write would double what a user must learn and keep consistent while deciding nothing kink-flow does not decide.
  2. *The harness's KORE-state inputs and term paths name the compiled configuration, not the specification.*
     A test is an input whose expected result is what the specification computes, and that computation starts at the configuration the specification's initializer builds from the inputs.
     A KORE state bypasses the initializer: it can be a configuration no input produces, so a kill from it can be a difference only on configurations the specification never reaches, a fact about the rewrite relation rather than about the specification's behavior; and it names compiled symbols, so a corpus written that way breaks whenever the way the specification compiles changes.
     A term path names a child-index position of the compiled configuration: it depends on the compiled cell layout, a path an end lacks makes the slot an error rather than a value, and a term-path slot gives no one-sided kill.
     Typed inputs name the specification's declared configuration variables and the constructors of their declared types, so they are stable under compilation and every one is a start the initializer builds.
     Cells named in the specification or in `[result] cells` are stable under compilation, a projection by them is defined on every configuration, and it is compatible with one-sided kills.
  3. *The harness keeps forms that kink's own tests need and no user corpus does.*
     Campaigns of generated mutants over many definitions, pinned sources, process isolation, a digest-checked store, resume and `replay-check` exercise engine paths that have no other end-to-end route; a user's corpus tests one specification, and kink-flow's caches are keyed by content digests and kink's build.

  Accepted cost: kink-corpus's tally and score are not kink-flow's counts.
  The statuses the two share are the campaign runner's, and each has one name in kink-campaign's reports (a mutant's `status` and its tally key), kink-corpus's summary and kink-flow's documents (kink-flow `tests/statuses.rs`); kink-flow's only other statuses, `unkillable` and `invalid-mutation`, are its own.
  Rejected: exposing KORE-state inputs or term paths in `FLOW.toml` (reason 2); deleting the harness binary (it is the only end-to-end route for generated campaigns, process isolation and the replay of stored reports, which kink's tests exercise); splitting the crate into a library and a harness crate (no document and no verdict changes, while the library's import sites in kink-flow would all move).
  Reopen on a user need that no form in the specification's own terms can serve.

- **U2 — one recorded killer per killed mutation, kept while it still kills.**
  `kink-flow run --lock FILE` (the krs front end: `kink/verdicts.lock` for the corpus's own mutation list) records each killed mutation's killer in a lock, which the corpus commits as it commits `Cargo.lock`.
  The killer is the recorded one while it is a comparable program of the corpus that kills the mutant; otherwise it is the first killing program in the search's order (the programs whose coverage witnesses the edit first, then the rest, each in `FLOW.toml`'s order).
  `run` rewrites the lock after a run that judged the whole list, and `--locked` writes nothing and makes a difference a finding (exit 1).
  There is no hint store in the cache and no cost order.
  [the single recorded killer is Sebastien's product decision, 2026-11-07; the rule settled from first principles]
  1. *A killer is a fact a reviewer reads.*
     A killer that depends on the cache or the clock moves in review for no reason the corpus or the specification gives, so the lock must be an input the run reads and a function of the inputs it writes.
  2. *Kept while it kills.*
     Re-checking the recorded killer by a run (or a record keyed by every input) makes a stale record cost a run, never a status or a wrong killer; dropping it on an unrelated edit would only repeat the search.
  3. *The replacement is canonical.*
     When no recorded killer kills, the first killer in the search's order is a function of the inputs, computed from keyed facts by the predicate the live call and tier 1 share.

  Accepted cost: a run without a lock after a specification edit recomputes the canonical prefix up to each killer, where a cache-held hint ran one program.
  Rejected: the full rendering as the lock, which costs every cell of every mutation (Foldiboy measured 81 against 11 calls when a case is added); a cache-held hint, because its killer depends on the cache; a cost order, because its killer depends on the clock; partial writes under `--only`, because they give a lock nobody checked; program digests in the lock, which are unreadable and hide renames.
  Reopen on a use where killer stability across corpus edits is not wanted.

## O. Observations

- **O1 — A corpus compares runs by declared observation channels; each class states its stuttering, and a survivor that rests on a horizon stays `survived` with its horizon.**
  `[observe]` declares point classes (rewrite rules on their before or after side, cells, and a stuttering mode, `collapse` or `count`, with no default) and logs (a `List` cell read at named classes' events and where the path ends), and every run is compared by them besides its end (kink-flow README, "What a run observes"; kink's `trust.md`, "What a kill trusts").
  A baseline run that a deterministic bound cuts before it ends is `comparable-prefix`, compared by its channels up to their horizons.
  A mutant that agrees up to every horizon is `survived`, and its row and its verdicts rendering carry `horizon`; one whose every horizon is 0 is `unknown`.
  Only one path per side is compared: a channel opens at its side's first state with several successors.
  [Sebastien, 2026-11-07: the stuttering mode declared per class, the survivor with its horizon, and the single-path meaning first, the prefix-set meaning for several paths a later unit]
  1. *An observation is a function of a finite prefix.*
     Every element is read in a reached state of a path the run explored, as a value under the baseline's definition, at an index that is a fact of the path; so a decided difference is a difference of the two definitions' observations in every model, and a bound only ends what is known: budget exhaustion never kills.
  2. *Which stuttering is meant is a property of the specification.*
     Weak trace equivalence over declared labels counts events (two equal consecutive events are two), while a position is a place to sample, not content, which collapses them; each loses kills the other finds (a redundant write under `count`; an idle cycle that is a promised event under `collapse`), and both are sound, so the author states which the specification promises.
  3. *A horizon qualifies a survivor as the declared observation does.*
     Every survivor is relative to what is compared; a horizon is part of the observation of a program that never ends, a function of the budget and not of the host, so it is reported with the survivor rather than as another status.
  4. *The K front end compares cells as they hold them.*
     kink-flow reads terms of a K definition and has no observer to evaluate a function in, so it refuses `observer`, `views`, `components`, `when` and `element`; identity contents and logs are sound at the K level by the end projection's argument.

  Accepted cost: a nondeterministic baseline is compared only up to its first branching; `query` and `fuzz` refuse a corpus with `[observe]` until their searches compare channels.
  Rejected: a default stuttering mode (reason 2); a separate status for a survivor on a prefix (reason 3); cutting a channel at a mutant's budget as a difference (reason 1).
  Reopen on a specification whose promised observation needs several paths before the prefix-set meaning lands.
