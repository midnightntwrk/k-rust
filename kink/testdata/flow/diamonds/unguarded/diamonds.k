// Flow fixture (fz26 KINK-PATHSET-FALLBACK, S9, the baseline direction): ../diamonds.k without
// the end rule's guard, so the baseline itself ends `go(N, 0)` in one undefined step at
// `go(0, 0)`. The mutation `end-guard-added` restores the guard: the mutant is stuck there.
module DIAMONDS-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= go(Int, Int) [symbol(go)]
                | l(Int, Int)  [symbol(l)]
                | r(Int, Int)  [symbol(r)]
                | fin(Int)     [symbol(fin)]
endmodule

module DIAMONDS
  imports DIAMONDS-SYNTAX
  imports INT
  configuration <k> $PGM:Prog </k>
  rule [gl]:  go(N, D) => l(N, D) requires N >Int 0
  rule [gr]:  go(N, D) => r(N, D) requires N >Int 0
  rule [lg]:  l(N, D) => go(N -Int 1, D)
  rule [rg]:  r(N, D) => go(N -Int 1, D)
  rule [end]: go(0, D) => fin(100 /Int D)
endmodule
