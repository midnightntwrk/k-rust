// A user sort's projection applied by a rule: `project:Exp`, which kompile declares with the
// equation `project:Exp(kseq(inj{Exp,KItem}(V), dotk)) = V`, read as a function with that equation.
module PROJUSER-SYNTAX
  imports K-EQUAL-SYNTAX
  syntax Exp ::= "z" [symbol(z)] | s(Exp) [symbol(s)]
  syntax Cmd ::= run(K) [symbol(run)] | done(Exp) [symbol(done)]
endmodule

module PROJUSER
  imports PROJUSER-SYNTAX
  configuration <k> $PGM:Cmd </k>
  rule [go]: <k> run(X) => done(project:Exp(X)) </k>
endmodule
