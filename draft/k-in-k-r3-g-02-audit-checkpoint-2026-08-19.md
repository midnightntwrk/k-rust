# R3-G-02 integration audit checkpoint — 19 August 2026

Status: stopped after three substantive full-oracle cycles; not integrated.

Worker commit `478ea271f7295e8eed4bafd6ea4fd13a5fbe1ffc` implements the
intended pre-CF/post-CF composition and finishes with a clean worktree. Its
third-cycle replay, `bun run check` (10/10), and `git diff --check` passed.
Frozen evidence hashes are:

- results: `a0d66432c3cf154f7d923b63d65a8f6c2c2868dc5d00204260648884d46ffdf7`;
- report: `910359d49626519af6dad71f11f6843add866542df01abd237048f44fef512ad`.

Root's static review repaired portable ordering, chained oracle identity
replacement, focused provenance collision/residual checks, the identity-hook
baseline, repeat operation/configuration comparisons, and evidence fields
before the final worker replay. Root then started a fresh workspace-aligned
detached replay, which crossed the identity baseline, both positives, every
pre-CF negative, and part of the post-CF suite without a path-stability error.

An independent read-only Sol audit nevertheless rejected integration for two
contract gaps:

1. `already-present` recognizes the trace name and `.List` body but does not
   compare the complete trace shell against the declared clone of the template.
   Shell properties, name-token sorts/attributes, and application/node metadata
   can differ while K and Java still accept it. Conflict coverage mutates only
   the body, not shape/metadata.
2. parsed configuration failure results accept any schema, reason, and
   canonical integer. The host does not enforce the contract schema, the closed
   reason set, nonnegative counts, or reason/count relationships before
   classifying the failure.

Both are explicit R3-G-02 acceptance requirements: one equal cloned trace cell,
same-name content/shape conflict, and malformed results failing at the
envelope. Root stopped the detached replay after the audit verdict. A passing
oracle cannot override those missing assertions.

R3-G-02A is the sole next leaf. It imports the stopped prototype only on its
repair branch, keeps both contracts and all runtime/portability behavior fixed,
and closes complete cloned-shell equality plus failure-envelope semantics.
Matching remains on hold.
