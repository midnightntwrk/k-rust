module LIVENESS-KRUN
  imports INT
  syntax State ::= start(Int)
  syntax State ::= probe(Int)
  syntax State ::= wrap(Int)
  syntax State ::= done()
  syntax Int ::= f(Int) [function, smtlib("f")]
  syntax Int ::= g(Int) [function, smtlib("g")]
  configuration <k> $PGM:State </k>
  rule g(_X) => 1 [simplification, smt-lemma]
  rule g(_X) => 2 [simplification, smt-lemma]
  rule <k> start(X) => probe(X) </k>
  rule <k> start(_X) => wrap(0) </k>
  rule <k> probe(X) => done() </k> requires X ==Int 0
  rule <k> wrap(X) => wrap(X) </k>
endmodule
