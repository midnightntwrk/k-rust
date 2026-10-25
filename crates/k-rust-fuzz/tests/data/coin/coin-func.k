// Mutant of coin.k whose added end is not data: for N <= 10 it is the baseline; for N > 10
// `flip(N)` ends with `opaque(N)` in <out>. `opaque` is declared `total` but has an equation
// only for N <= 10, so the leaf holds an unevaluated application of a total function. That leaf
// is ceil-free, yet its meaning depends on the definition's functions, so it fails condition 4
// of the differential target (ARCHITECTURE.md 4.3) and is never a kill.

module COIN-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= flip(Int)   [symbol(flip)]
               | count(Int)  [symbol(count)]
endmodule

module COIN
  imports COIN-SYNTAX
  imports INT
  imports BOOL

  syntax Int ::= opaque(Int)  [function, total, symbol(opaque)]

  configuration <k> $PGM:Pgm </k>
                <out> 0 </out>

  rule [opaque-small]: opaque(N) => N requires N <=Int 10

  rule [heads]:      <k> flip(N) => .K ... </k> <out> _ => N </out> requires N <=Int 10
  rule [tails]:      <k> flip(N) => .K ... </k> <out> _ => N +Int 1 </out> requires N <=Int 10
  rule [hide]:       <k> flip(N) => .K ... </k> <out> _ => opaque(N) </out> requires N >Int 10
  rule [count-step]: <k> count(N) => count(N -Int 1) ... </k> requires N >Int 0
  rule [count-done]: <k> count(N) => .K ... </k> <out> _ => 0 </out> requires N <=Int 0
endmodule
