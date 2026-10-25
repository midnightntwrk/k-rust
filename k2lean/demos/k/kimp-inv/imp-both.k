requires "imp-inv.k"

// A kind 1 invariant of kimp in the top-cell form whose right-hand side conjoins two partial
// calls: `envOk` and `storeNoIds` of kimpinv (imp-inv.k) together, as one function of the whole
// configuration. Its value at a configuration is a chain of two `Option.bind`s, which
// `Invariant.topBoth_cells` states and `KPrelude.bind_bool_eq_some_true` splits into the two
// facts the closers read (k2lean/docs/invariants.md, §3.1).
module IMP-BOTH
  imports IMP-INV

  syntax Bool ::= topBoth(GeneratedTopCell) [function, total]
  rule topBoth(<generatedTop> <k> _ </k> <env> E </env> _ </generatedTop>)
    => allValues(values(E)) andBool noIds(values(E))
endmodule
