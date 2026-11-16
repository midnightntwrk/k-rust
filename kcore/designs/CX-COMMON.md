# Counterexample pass: common brief (CX)

You are a Fable judgement agent. **Your job is to try to break designs that nobody has attacked yet, before any lane implements them.** Earlier lanes found every CN-3 defect so far with a concrete counterexample that the kernel checked. Examples: the `aside` reading, arm C of `rulesPlain`, the `fails_plain` pin, and V1's carrier clauses. Your job is to find the next ones now, on paper and in scratch Lean, not later in a lane.

Main directory, called MAIN below: /home/sebastiengllmt/git/workspaces/starstream-fv/inspirations/midnightntwrk/k-rust/draft-personal/k-semantics-core-2026-11

## What counts as a defect in a unit
A defect is any of the following.
1. **Unsound.** A K text, or a KCore `Semantics` value the reader could produce, at which the unit's Lean, as the design writes it, makes a pinned statement false. Unsound also covers a unit that lets `Γ` assert something the text's sentence does not entail or that the text refutes.
2. **Contradiction in Γ.** A text the unit admits at which `Γ c` (or `Γc c`) has no model, while the text's sorted theory does have one.
3. **Unprovable.** The unit's own statement or lemma is false as written, or needs a hypothesis it does not have.
4. **Wrong expectation.** A fixture expectation in the unit's table that disagrees with what the kompiled sentence means as a matching-logic theory, judged from first principles. A reference backend's behaviour is never a reason.
5. **Bad fit with what has landed.** The unit's Lean does not fit the merged line: a name that no longer exists, a field that moved, a conflict with a decision taken since CN-3.
6. **Construct gap.** A K construct the unit claims to cover that it neither supports nor refuses with a stated reason.

Not defects: style, cost, naming, or anything that only lowers performance.

## Settled; do not reopen
Each item has a file you may read.
- **HOOK-READING** (findings/HOOK-READING-decision.md): an open generator's laws are premises at every interpretation; OpenLaws is a named obligation; lawHooks is the inhabitation witness.
- **NONEMPTY** (findings/NONEMPTY-decision.md): Γ states no nonempty carriers. The reader exhibits a value where its law needs an element. Shapes at a sort without a value stay refused.
- **N1** (findings/N1-decision.md): Γ has no no-junk item at a sort with an empty generator list. At a Loop-like sort, the item is the text's one unfolding. A counterexample that needs Γ to make a generator-less sort empty is N-1, not a new finding.
- **F1-DECISION** (findings/F1-DECISION.md, §1–§7) and **R1-DECISION** (findings/R1-DECISION.md): `aside`, the `leftVars` range, the pins `fails_plain` and `notApplies_of_binds`, and `rulesPlain` arm C with `condApart`.
- **Owner directions** (TICKETS `[goal].direction`):
  - upstream semantics are dropped;
  - done means every K construct is supported or refused with a reason;
  - Set concatenation is nilpotent;
  - Γ has no contradictions;
  - headlines are not weakened.

## Reading set (closed)
MAIN files:
- designs/CN-3-merged-constructs.md: the "Annotations after U1" block first (it overrides the body), §2–§3 as your units need, §4 in full, and §5.
- findings/CN3-ADD-addendum.md.
- The four decision files above.
- designs/STAGE4-COMMON.md.
- TICKETS-2026-11-11.toml: only `[goal]` and the entries dated 2026-11-16.

Lean trees, read-only:
- The lane trees that hold what has landed in your area. Your area brief names them.
- /artifacts/worktrees/kcore-merge/draft-personal/k-semantics-core-2026-11/kcore-spec at 0e4ddd03, the BASE-1 line.
- Note that INT is merging all lanes in kcore-merge right now. Its working copy may be mid-merge, so read kcore-merge only through `jj file show -r 0e4ddd03 <path>`.

Fixtures, read-only: constructs/fixtures/ and f2-examples/ in any of these trees. Read only the sentences you need.

**Reading outside this set:** first write down why you need it, then do it only if it is one named Lean declaration or one fixture sentence. Anything larger is a STOP: report what you need. List every file you read in your output.

## Scratch checks
Kernel-check counterexamples where it is cheap. A checked counterexample is worth far more than an argued one. Rules:
- Put scratch files in the scratchpad directory your area brief names.
- Run `lake env lean <file>` from a lane tree's package root, under `LEAN_NUM_THREADS=1 systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 timeout 1200`, with one lean process at a time.
- Do not edit any tree, and do not build a tree. If the tree's .olean files are missing or stale, write the check as "to run" instead of building.
- Nothing that uses sorry, axiom or native_decide counts as checked.

## Output
Write one file, MAIN/findings/CX-<AREA>.md. It does not need to be committed; I commit it. For each unit (and each fixture expectation) give:
- **Verdict:** valid as written / defect (kind 1–6) / cannot judge from the reading set (and what is missing).
- **For a defect:** the counterexample (the text or `Semantics`, and the statement that fails), whether it was kernel-checked (file:line of the scratch file) or argued, and a proposed fix with its reason and reversal criterion. The proposal is not a decision; CN-4 decides.
- **For "valid":** the one strongest attack you tried and why it failed.

End the file with:
- a table: unit, verdict, kind, checked or argued;
- a list of the declarations each proposed fix touches, with their owners (CN-3 §4).

Hand back at most 30 lines: the table, and the defects in order of severity.
