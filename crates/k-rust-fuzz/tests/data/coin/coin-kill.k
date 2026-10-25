// Mutant of coin.k that adds an end on some inputs: for N <= 10 it is the baseline; for
// N > 10 `flip(N)` has the single end N + 2, which is not in the baseline's set {N, N + 1}.
// A differential campaign over the hole in `flip(3)` must find N > 10.

module COIN-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= flip(Int)   [symbol(flip)]
               | count(Int)  [symbol(count)]
endmodule

module COIN
  imports COIN-SYNTAX
  imports INT
  imports BOOL

  configuration <k> $PGM:Pgm </k>
                <out> 0 </out>

  rule [heads]:      <k> flip(N) => .K ... </k> <out> _ => N </out> requires N <=Int 10
  rule [tails]:      <k> flip(N) => .K ... </k> <out> _ => N +Int 1 </out> requires N <=Int 10
  rule [skew]:       <k> flip(N) => .K ... </k> <out> _ => N +Int 2 </out> requires N >Int 10
  rule [count-step]: <k> count(N) => count(N -Int 1) ... </k> requires N >Int 0
  rule [count-done]: <k> count(N) => .K ... </k> <out> _ => 0 </out> requires N <=Int 0
endmodule
