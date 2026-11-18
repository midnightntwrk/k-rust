// A constructor with named arguments, `pair(fst: Foo, snd: Foo)`. kompile declares the
// projections of its arguments, `project:pair:fst` and `project:pair:snd`, and writes their
// equations `project:pair:fst(pair(K0, K1)) = K0` and `project:pair:snd(pair(K0, K1)) = K1`;
// no sentence of the definition applies them.
module NAMEDARG-SYNTAX
  syntax Foo ::= "leaf" [symbol(leaf)] | pair(fst: Foo, snd: Foo) [symbol(pair)]
  syntax Cmd ::= run(Foo) [symbol(run)] | done(Foo) [symbol(done)]
endmodule

module NAMEDARG
  imports NAMEDARG-SYNTAX
  configuration <k> $PGM:Cmd </k>
  rule [go]: <k> run(pair(X, _)) => done(X) </k>
endmodule
