// Baseline of the differential fixtures. `flip(N)` ends with N or N + 1 in <out>: two paths
// whose single ends differ, and whose set of ends is {N, N + 1}. `count(N)` takes N + 1 steps,
// so a depth bound below that leaves the baseline incomplete.

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

  rule [heads]:      <k> flip(N) => .K ... </k> <out> _ => N </out>
  rule [tails]:      <k> flip(N) => .K ... </k> <out> _ => N +Int 1 </out>
  rule [count-step]: <k> count(N) => count(N -Int 1) ... </k> requires N >Int 0
  rule [count-done]: <k> count(N) => .K ... </k> <out> _ => 0 </out> requires N <=Int 0
endmodule
