// Mutant of coin.k that changes only layout and comments: the compiled definition is the
// baseline's up to source positions, so the execution digests and rewrite orders are equal.
module COIN-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= flip(Int) [symbol(flip)] | count(Int) [symbol(count)]
endmodule

module COIN
  imports COIN-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Pgm </k> <out> 0 </out>

  // The two sides of the coin.
  rule [heads]: <k> flip(N) => .K ... </k>
                <out> _ => N </out>
  rule [tails]: <k> flip(N) => .K ... </k>
                <out> _ => N +Int 1 </out>

  // A countdown.
  rule [count-step]: <k> count(N) => count(N -Int 1) ... </k>
    requires N >Int 0
  rule [count-done]: <k> count(N) => .K ... </k> <out> _ => 0 </out>
    requires N <=Int 0
endmodule
