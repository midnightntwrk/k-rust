# Proposal 05: The full K-mirror DSL — assessed, and mostly redirected

For completeness: the maximal option is a function-like macro that embeds
K-shaped syntax wholesale, so IMP reads at K's density inside a Rust file:

```rust
k::semantics! {
    syntax Expr ::= "-" Expr            [strict]
                  > left:
                    Expr "*" Expr       [seqstrict]
                  | Expr "/" Expr       [seqstrict]
                  // ...

    configuration {
        <k color="green"> $PGM: Stmt </k>
        <env color="yellow"> $ENV: Map </env>
    }

    rule [assign]: <k> Assign(X, V:Value) => .K ... </k>
                   <env> E => E[X <- V] </env>
}
```

This would win every line-count comparison in this folder. It is still the
wrong primary surface for this project, for reasons that are already on the
record and that the internals inventory makes concrete:

1. **It abandons the project's core bet.** The charter's premise is that
   Rust item shapes are what engineers and coding agents already read and
   write fluently. A K-mirror block is K with extra steps — anyone fluent
   enough to read it fluently can read `.k` files, and the workspace already
   has those.
2. **r3 already adjudicated this** for rules: *"most of the important file
   becomes opaque token trees to Rust tooling; it invents another item
   grammar; and agents lose ordinary function, pattern, attribute, and body
   cues. Retain only as a raw/advanced escape hatch"*
   (`draft/investigations/r3-rule-surface.md:232-235`). r4 kept `k::grammar!`
   in the design as exactly that — an unimplemented escape hatch for grammar
   sentences the attribute surface cannot express.
3. **It fights four architectural gates at once** (internals inventory §4.8):
   the collector re-parses authored source and would need a complete second
   K-ish parser with byte-exact anchor reproduction; the LSP oracle's
   goto-def/hover/rename requirements have no plausible implementation over
   productions that exist only inside one macro's tokens; the span-derived
   item-name nonce makes every declaration in the block position-sensitive
   unless a parallel naming scheme is built; and the `ProvenanceRole`
   catalog would need wholesale extension.
4. **Semantic honesty erodes at the edges.** Inside a K-mirror block,
   nothing distinguishes the parts that are typed and validated by KRS from
   parts that pass through raw — the reader must know. The attribute
   surface makes that boundary structural (`#[k::raw_attr]` vs typed
   attributes).

## What survives from this direction

Two genuinely useful ideas hide inside the maximal proposal:

### 05a. Keep `k::grammar!` / raw K as a narrow escape hatch (already designed)

Per r4 and the charter's "lossless access to K": a marked raw island for the
constructs the typed surface cannot yet express. Nothing new to decide here
— just noting that its existence is not an argument for widening it.

### 05b. Invert the direction: read in K, write in Rust

The workspace goal is spec-driven development with machine-checkable
oracles; reviewers may prefer K's density even when authors and agents work
in KRS. KRS already emits canonical `.k` with a full source map
(`crates/krs-compiler/src/emit.rs`, `sidecar.rs`) — as a *debugging*
artifact. Promote it to a *review* artifact:

- `krs view <item>` (or a rustdoc-style HTML view) renders the K form of any
  rule/sort/module next to its KRS source, using the existing
  `SymbolMap`/`SourceMap` to hyperlink both ways.
- CI posts the generated-`.k` diff alongside the Rust diff on every change,
  so a reviewer reads the semantics delta at K density (one line per rule)
  while the author edited Rust.

This captures most of what the K-mirror DSL promises — K-density *reading* —
at near-zero design risk, with no new surface, no new parser, and no tooling
regression, because it composes two things that already exist. It also
directly serves the workspace's actual review workflow (humans auditing
agent-written semantics).

## Recommendation

Reject the K-mirror block as an authoring surface (reaffirming r3/r4).
Adopt 05b as cheap tooling with outsized review value; keep 05a scoped to
its escape-hatch role.
