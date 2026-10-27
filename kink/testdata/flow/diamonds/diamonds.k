// Flow fixture (fz26 KINK-PATHSET-FALLBACK, S9): a guarded division after N diamonds. Each
// diamond `go -> l | r -> go` converges, so a path set visits about 3 * 2^N states and a state
// set about 4 * N. `go`, `l`, `r` and `fin` are constructors, so `go(0, 0)` is data in both
// definitions. The end rule's guard is what the mutation `end-guard-dropped` drops: then
// `go(N, 0)` ends in one undefined step (`100 /Int 0`) at `go(0, 0)`, which the state set
// reports once and the path set once per path.
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
  rule [end]: go(0, D) => fin(100 /Int D) requires D =/=Int 0
endmodule
