module E2-OPEN-GENLESS-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Empty
  syntax Loop ::= loop(Loop) [symbol(loop)]
  syntax Pgm ::= go(Int) [symbol(go)] | done(Int) [symbol(done)]
endmodule

module E2-OPEN-GENLESS
  imports E2-OPEN-GENLESS-SYNTAX
  imports INT
  imports BOOL
  syntax Bool ::= f(Empty) [function, symbol(f)]
  syntax Int ::= g(KItem) [function, symbol(g)]
  rule g(_:Empty) => 1
  rule g(_) => 0 [owise]
  configuration <k> $PGM:Pgm </k>
  rule <k> go(I) => done(I) </k> requires g(E:Empty) ==Int 1 [unboundVariables(E)]
endmodule
