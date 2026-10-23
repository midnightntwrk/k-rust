// Mutant of claimstep.k: the guard of `go` is dropped. On `go(0)` the right-hand side
// `10 /Int 0` is undefined, so the step is undefined (a `trivial` leaf) and no claim is involved:
// the mutant has no final configuration where the baseline ends at `go(0)`, a removed end.

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

  rule [go]: <k> go(N) => .K ... </k> <out> _ => 10 /Int N </out>
endmodule
