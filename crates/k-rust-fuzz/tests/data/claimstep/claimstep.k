// Baseline of the claim pair (FZ-DIFFEND). `go(N)` ends with `10 /Int N` in <out> for N =/= 0;
// `go(0)` is an abnormal stop: no rule applies to it, so `go(0)` stays on <k>, a clean final
// configuration.

module CLAIMSTEP-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= go(Int)  [symbol(go)]
endmodule

module CLAIMSTEP
  imports CLAIMSTEP-SYNTAX
  imports INT
  imports BOOL

  configuration <k> $PGM:Pgm </k>
                <out> 0 </out>

  rule [go]: <k> go(N) => .K ... </k> <out> _ => 10 /Int N </out> requires N =/=Int 0
endmodule
