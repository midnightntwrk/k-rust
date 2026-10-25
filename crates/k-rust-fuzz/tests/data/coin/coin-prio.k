// Mutant of coin.k in which `tails` takes precedence over `heads`: `flip(N)` has the single end
// N + 1, which is in the baseline's set {N, N + 1}. The mutant removes an end and adds none.

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
  rule [tails]:      <k> flip(N) => .K ... </k> <out> _ => N +Int 1 </out> [priority(40)]
  rule [count-step]: <k> count(N) => count(N -Int 1) ... </k> requires N >Int 0
  rule [count-done]: <k> count(N) => .K ... </k> <out> _ => 0 </out> requires N <=Int 0
endmodule
