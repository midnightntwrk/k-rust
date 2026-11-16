// A library sort's projection applied by a rule: `project:Int`, read as a function from krust's
// text, which holds its equation `project:Int(kseq(inj{Int,KItem}(V), dotk)) = V`, its
// selector-domain axiom `⌈project:Int(K)⌉ = ∃V. K = kseq(inj{Int,KItem}(V), dotk)` and its
// selector-inverse lemma.
module PROJAPP-SYNTAX
  imports INT-SYNTAX
  imports K-EQUAL-SYNTAX
  syntax Cmd ::= run(K) [symbol(run)] | done(Int) [symbol(done)]
endmodule

module PROJAPP
  imports PROJAPP-SYNTAX
  imports INT
  configuration <k> $PGM:Cmd </k>
  rule [go]: <k> run(X) => done(project:Int(X)) </k>
endmodule
