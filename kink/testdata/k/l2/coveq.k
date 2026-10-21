// Re-pin L2-1 coverage fixture (GUARDEDEQ-style, without claims): `load` decides its condition
// with the function `norm`. A run of `load(addr(1))` applies the equation `norm`; a run of
// `load(addr(-1))` begins to decide `norm`'s condition, which fails, and applies `normNeg`, which
// has a lower priority, so `norm` is scanned first; a run of `store` reaches neither. Coverage v2
// orders an edit of `norm`'s right-hand side by the runs that applied it and an edit of its
// `requires` by the runs that matched it.
module COVEQ-SYNTAX
  imports INT-SYNTAX
  syntax Address ::= addr(Int) [symbol(addr)]
  syntax Op ::= load(Address, Int) [symbol(load)]
              | store(Address, Int) [symbol(store)]
  syntax Prog ::= "halt" [symbol(halt)]
                | seq(Op, Prog) [symbol(seq)]
endmodule

module COVEQ
  imports COVEQ-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  configuration <k> .K </k>

  syntax Int ::= norm(Int) [function, symbol(norm)]
  rule [norm]:    norm(X) => X requires X >=Int 0
  rule [normNeg]: norm(X) => 0 -Int X requires X <Int 0 [priority(60)]

  rule [store]: seq(store(addr(_), _), P) => P
  rule [load]:  seq(load(addr(A), _), P) => P requires norm(A) ==Int A
endmodule
