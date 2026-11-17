# kcore-spec: the core of K's semantics (`KCore`), and KORE to applicative matching logic

State: milestone 1, step M1.2 ([../milestone-1/README.md](../milestone-1/README.md)), 2026-11-05, for Sebastien's review.
This package translates a KORE definition (read by [../kore-lean](../kore-lean)) into a theory of applicative matching logic over [../aml-port](../aml-port)'s `Pattern`, and builds Γ_D for `../milestone-1/kore/definition.kore`.
M1.3 (2026-11-06) adds the specification: the fragment F0, the curated Γ_D with Γ_cons, the closure axiom, and the statements (soundness and completeness, step equivalence), reviewed in [STATEMENTS.md](STATEMENTS.md). F0 is a typed structure `F0Def` = (semantic core, KORE presentation, termination certificate) with a generator `emit` to kompile's KORE and an exact round-trip check (decision `Q-f0-shape`, STATEMENTS.md §1).

Review documents:

- [TRANSLATION.md](TRANSLATION.md): every rule with its source or marked CHOICE, the choices needing a decision, the gaps in the sources, and findings about kompile's theory.
- [SAMPLE.md](SAMPLE.md): 15 KORE axioms (and the declarations and encoding axioms they rest on) beside their translation.
- [GAMMA_D.txt](GAMMA_D.txt): all of Γ_D in the papers' notation (`lake exe gammad > GAMMA_D.txt`).
- [STATEMENTS.md](STATEMENTS.md) (M1.3): F0, Γ_cons, the closure axiom, the statements, choices and open questions.
- [GAMMA_CONS.txt](GAMMA_CONS.txt) (M1.3): for the subject, the F0 verdict, Γ_cons, Γ_closure and the simplification lemmas (`lake exe gammad --spec > GAMMA_CONS.txt`).

## Layout (P1.4, 2026-11-09: one core, `KCore`; P2.1: the generator)

F0 and F1 were removed and F2 became `KCore` (../findings/P1.4-invariants-certificates-kcore.md). The specification is [KCORE-SPEC.md](KCORE-SPEC.md) with its audit [KCORE-AUDIT.md](KCORE-AUDIT.md); F1-SPEC.md, F1-AUDIT.md, STATEMENTS.md and the M1 documents above describe removed code and are history.

| Path | Content |
|---|---|
| `KcoreSpec/Kore/` (namespace `KoreAML`) | the KORE-to-matching-logic translation and the KORE helpers the core shares with it: `Signature`, `Translate` (`Theory.ofDefinition`), `Print`, `Import` (`kore_definition`), `Subject` (peano's KORE, `KoreAML.Peano.kore`), `Base` (locations, ids, `CtorSig`, generators), `Build` (KORE builders `emit` uses), `Read` (KORE readers `parse` uses), `Reorder` (`Reordered` and its permutation-hint check `Tie`), `ReorderTheory` (reordering keeps the models), `Gamma` (Γ_cons's items, the closure disjunct), `Blocks` (a permutation of blocks checked a slice at a time), `Distinct` (distinct strings by sorted codes), `KoreTerm` (`kore_term`, the KORE in segments), `KernelRfl` |
| `KcoreSpec/*.lean` (namespace `KCore`) | the core, as F2 had it (KCORE-SPEC.md): frozen `FixedSignature` (the registry), `Core`, `Value`, `Hooks`, `Evaluation`, `Step`; reviewed `Definition`, `DefinitionWf`, `Prelude` (the six fixed texts), `Emit`, `Tie` (`wf`, `Tied k`, and the tie from its parts), `Statements` (what the statements are built from, `Obligations`), `Sound` (`KCore.Sound`, `KCore.Complete`; `sound` and `complete` proved from `wf` and `Obligations`, no `sorry` in the library); unreviewed `Parse` (with `classify` and `Refusal`) and `Account` (the reading's account, compiled); checked `Exec`, `StepIff`/`StepIffWf` (`step_iff`), `SubjectReduction`, `NamesApart`, the matcher and evaluation proofs, `Determinism`/`DetSound`, `Params`, `Features`, `Invariant` (the invariant theorem kind), `Cert` (run certificates), `DataCmd`, `Checks`; `Examples` |
| `KcoreSpec/ReviewCone.lean` | `#review_cone`, the review-cone meta program |
| `GammaD.lean` | `lake exe gammad [file] [--axioms i,j,…] [--raw i,j,…]` |
| `KcoreSpec/Tables.lean`, `TablesChecked.lean` | a definition's derived tables as an argument of the checked decisions (A5, P2.1) |
| `KcoreGen.lean`, `gen/` | the generator, `kcore gen definition.kore OUTDIR NAME [--tie]` (`lake build kcore`; `gen/gen.sh`): the package without the tie, its tie with `--tie`; it prints each sentence class's count and stops with the reader's refusals; and the generic build of a package (`gen/build.sh`) (P2.1) |
| `examples/` | the example definitions' generated packages (`peano` with its tie; `prio`, `kink-imp`, `kimp`, `imp-sec`, `imp-sec-leaky`, `ph`, `kryp`, `vault`, `vault-leaky`, `colls-list`, `lazy`, `fprio`, `colls`, `ref-peano`, `ref-fprio`, `ref-kimp` with `--wf`), each with its user's modules (`User/`), and kimp's noninterference over several packages (`kimp-ni`); `examples/run.sh` regenerates and builds them (`--build-only`: builds them as committed) |
| `test/Member.lean`, `test/member.sh`, `test/ni-kore.sh` | why each KORE text is or is not in KCore, and the registry hooks checked against the builtin texts; kimp's and its checker's KORE compiled |
| `test/ReviewCone.lean`, `test/OpaqueAudit.lean`, `test/PrintNames.lean` | the review cones, the opaque-constant audit, the numbering printer |
| `../findings/work/p14/tie/` | F1's tie of 34 definitions over KCore (`run.sh`) |

## Running

```sh
test/lake-serial.sh                 # the library, one module at a time, each under a 12 GiB memory scope
lake build gammad && lake exe gammad > GAMMA_D.txt
test/integration.sh                 # once per merged batch (test/README.md)
test/release.sh                     # the release run: integration, every example package built, their axioms
examples/run.sh                     # the example packages (generated), peano's tie, their users' modules
test/member.sh                      # membership diagnostics and the registry hooks
lake env lean test/ReviewCone.lean  # the review cones
../findings/work/p14/tie/run.sh     # F1's 34 definitions tied over KCore
```

## Results of M1.2 (history; 2026-11-05, shared host, load average 50–98)

- Γ_D: 343 axioms, 141 of the encoding (Γ^AML: 1 definedness, 18 sort, 18 nonempty, 1 sorts, 96 arity, 2 sorted definedness, 1 `•` arity, 4 `\dv` arity) and 202 translated axioms, one per KORE axiom.
  As a tree it has 154,838 AML pattern nodes for the KORE's 2,374: about 65 times as many, because KORE's connectives are expanded through the MmL notations they abbreviate and through AML's own derived connectives (TRANSLATION.md, "Shape of Γ_D").
- Elaboration: `KcoreSpec/Subject.lean` (read the 107 kB KORE, parse, build the AST term, add and compile it, define Γ_D) takes 2.2 s and 1.67 GB peak, of which `import Lean` alone takes 1.0 s and 1.60 GB.
  `KcoreSpec/Checks.lean` takes 2.7 s.
  A clean `lake build` of this package (including the C compilation of the dependencies for `gammad`) took 21 s.
- `gammad`: parse 3–14 ms, translation under 1 ms, printing 20–56 ms.
- Kernel: `decide +kernel` reduces the whole translation; `ΓD_noUntranslated` (no untranslated node anywhere in Γ_D) and `ΓD_sizes` check in 20–25 s and depend only on `propext`, `Classical.choice`, `Quot.sound`.
  So M1.4 can unfold Γ_D's axioms by evaluation; the derived `BEq` of kore-lean's nested `KSort` is not kernel-reducible and is not used (`decide (a = b)` instead).

Checks in `Checks.lean`: the axiom count is 202 before and after (kernel); no untranslated node; every symbol, sort and `\dv` literal occurring in Γ_D is declared or has its arity axiom; every declared symbol has one arity axiom and every sort one sort axiom; every variable index is in its axiom's table; the well-sortedness guard of each translated axiom covers every free variable of its body ((7.11)); the subject's construct counts (`\top` 256, `\equals` 194, `\in` 80, `\exists` 134, `\dv` 36, `\ceil` 34, `\bottom` 30, `\rewrites` 2, set variables 6, no `\mu`, `\nu`, `\forall`, `\floor`, `\next`); every `\in` has a variable on the left; the sort-parameter lists; aliases declared but never applied.

## Notes for M1.3 and M1.4

- `Subject` imports `Lean` (through `Import`), so every module that imports Γ_D pays `import Lean`'s cost.
- `Theory.premises` contains aml-port's `definedness` at every variable, so `HasDefinedness ΓD.premises` holds and aml-port's definedness lemmas apply.
- Findings F1 and F2 of TRANSLATION.md bear directly on M1.4: as emitted, Γ_D is false in the intended interpretation of injections into `KItem` (axiom 3) and of `Map` (axiom 202).
