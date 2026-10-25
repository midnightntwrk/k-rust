// Mutant of claimstep.k: the guard of `go` is dropped and the rule claims
// `preserves-definedness`, which `go(0)` contradicts: its result `10 /Int 0` is undefined. The
// undefined step's leaf carries the contradicted claim, so the step is no evidence.

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

  rule [go]: <k> go(N) => .K ... </k> <out> _ => 10 /Int N </out> [preserves-definedness]
endmodule
