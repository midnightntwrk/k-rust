// fz26 FZ-FRESH, K-COUNTER: `go(N)` mints `1` fresh value with a one-name rule, discards it and
// ends in `done(N)`. The mutant `mint(0)` of `go` mints none, so the two ends differ only in the
// content of `<generatedCounter>` (1 against 0), which a whole-term slot does not compare.
module COUNTER-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= go(Int) [symbol(go)]
                | done(Int) [symbol(done)]
endmodule

module COUNTER
  imports COUNTER-SYNTAX
  imports INT
  imports BOOL
  syntax KItem ::= mint(Int) [symbol(mint)]
                 | tmp(Int) [symbol(tmp)]
  configuration <k> $PGM:Prog </k>

  rule [go]:   <k> go(N) => mint(1) ~> done(N) </k>
  rule [mint]: <k> mint(I) => tmp(!_X:Int) ~> mint(I -Int 1) ... </k> requires I >Int 0
  rule [stop]: <k> mint(I) => .K ... </k> requires I <=Int 0
  rule [tmp]:  <k> tmp(_) => .K ... </k>
endmodule
