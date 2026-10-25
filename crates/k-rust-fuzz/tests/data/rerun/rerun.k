// The re-run pair (INT7): `go(N)` has three ends, `a(N)`, `c(N)` and `b(opaque(N))`, where
// `opaque` is a `total` function with no equation, so the last end is clean but not data (it is
// not constructor-only). Strategy `any` follows `ga` (written first).

module RERUN-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= go(Int)  [symbol(go)]
endmodule

module RERUN
  imports RERUN-SYNTAX
  imports INT

  syntax KItem ::= a(Int) | b(Int) | c(Int)
  syntax Int ::= opaque(Int)  [function, total, symbol(opaque)]

  configuration <k> $PGM:Pgm </k>

  rule [ga]: <k> go(N) => a(N) ... </k>
  rule [gc]: <k> go(N) => c(N) ... </k>
  rule [gb]: <k> go(N) => b(opaque(N)) ... </k>
endmodule
