// Mutant of coin.k with `tails` written before `heads`. The rules are the baseline's, so the
// set of ends of every program is the baseline's; only the source rewrite order differs, which
// selects the path that strategy `any` follows on the source-execution route.

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

  rule [tails]:      <k> flip(N) => .K ... </k> <out> _ => N +Int 1 </out>
  rule [heads]:      <k> flip(N) => .K ... </k> <out> _ => N </out>
  rule [count-step]: <k> count(N) => count(N -Int 1) ... </k> requires N >Int 0
  rule [count-done]: <k> count(N) => .K ... </k> <out> _ => 0 </out> requires N <=Int 0
endmodule
