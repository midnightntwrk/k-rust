// Cell-less rules whose sides have two common supersorts in the main module's view. Compilation
// wraps each in the computation cell, where each side is an item of the `<k>` sequence, so the
// sides need no least upper bound: LUBBB's `ab` sees one supersort of `A` and `B` (`C`), and the
// main module adds a second (`D`); `main-ab` is declared where both are visible; `pz` writes a
// parametric application on a right side, which compilation instantiates at the cell's content
// sort.
module CELL-LESS-BOUND-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int) [symbol(go)]
endmodule

module LUBBB
  imports INT-SYNTAX
  syntax A ::= a(Int) [symbol(a)]
  syntax B ::= b(Int) [symbol(b)]
  syntax C ::= A | B
  rule [ab]: a(X) => b(X)
endmodule

module CELL-LESS-BOUND
  imports CELL-LESS-BOUND-SYNTAX
  imports LUBBB
  imports INT
  syntax D ::= A | B
  syntax {S} S ::= pz(Int) [symbol(pz)]
  configuration <k> $PGM:Pgm </k>
  rule [go]: go(X) => a(X)
  rule [main-ab]: a(X) => b(X)
  rule [pz]: a(X) => pz(X)
endmodule
