// Baseline of the undeclared-symbol pair (FZ-ENGINE-R4 review B1). `done(Int)` has no `symbol`
// attribute, so its KORE label is generated from the module that declares it, `R-SYNTAX`.
// `go(N)` rewrites to `done(N)` in one step.

module R-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= go(Int)  [symbol(go)]
               | done(Int)
endmodule

module R
  imports R-SYNTAX
  imports INT

  configuration <k> $PGM:Pgm </k>

  rule <k> go(N) => done(N) </k>
endmodule
