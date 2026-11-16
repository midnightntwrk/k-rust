// Functions of the definition's own, not declared total, applied as map keys in rules' left
// sides, their arguments bound by the rest of the left side: `pidx(B, I)` has no value where I is
// neither 0 nor 1, `kf(I)` (result sort Key) none where I is not 1. `get` beside an `[owise]` rule
// (`miss`), `put` with a `requires`, `look` with a key of a sort other than Int. (Partial by their
// patterns: with an equation `requires`, K 7.1.337's Haskell backend stops validating the text,
// "cannot compact functions".)
module KEYFN-PARTIAL-SYNTAX
  imports INT-SYNTAX
endmodule

module KEYFN-PARTIAL
  imports KEYFN-PARTIAL-SYNTAX
  imports INT
  imports MAP
  imports BOOL
  syntax Int ::= pidx(Int, Int) [function, symbol(pidx)]
  rule pidx(B, 0) => B
  rule pidx(B, 1) => B +Int 1
  syntax Key ::= k(Int) [symbol(k)]
  syntax Key ::= kf(Int) [function, symbol(kf)]
  rule kf(1) => k(1)
  syntax KItem ::= get(Int) [symbol(get)] | put(Int, Int) [symbol(put)] | look(Int) [symbol(look)]
                 | miss() [symbol(miss)]
  configuration <k> $PGM:KItem </k> <base> 0 </base> <mem> .Map </mem> <tab> .Map </tab>
  rule <k> get(I) => V ... </k> <base> B </base> <mem> pidx(B, I) |-> V ... </mem>
  rule <k> get(_) => miss() ... </k> [owise]
  rule <k> put(I, W) => W ... </k> <base> B </base> <mem> pidx(B, I) |-> _ ... </mem>
    requires W >Int 0
  rule <k> look(I) => V ... </k> <tab> kf(I) |-> V ... </tab>
endmodule
