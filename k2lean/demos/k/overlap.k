// A definition with one genuine overlap, for the gate's determinism checks (k2lean/tests/gate.sh,
// library `ovl`): `go(N)` with 0 < N < 10 rewrites by two rules to different configurations
// (listed in `overlaps` and witnessed), `set(N)` with N >= 100 by two rules to the same one
// (joinable, so not listed), and the other pairs of rules never apply at once.

module OVERLAP-SYNTAX
  imports INT-SYNTAX
  syntax Cmd ::= "go" "(" Int ")"  [symbol(go)]
               | "set" "(" Int ")" [symbol(set)]
endmodule

module OVERLAP
  imports OVERLAP-SYNTAX
  imports INT

  configuration <k> $PGM:Cmd </k> <out> 0 </out>

  rule <k> go(N) => .K ... </k> <out> _ => N </out> requires N >Int 0
  rule <k> go(N) => .K ... </k> <out> _ => 0 -Int N </out> requires N <Int 10

  rule <k> set(N) => .K ... </k> <out> _ => N </out> requires N >=Int 100
  rule <k> set(N) => .K ... </k> <out> _ => N </out> requires N >=Int 50
  rule <k> set(N) => .K ... </k> <out> _ => 1 </out> requires N <Int 50
endmodule
