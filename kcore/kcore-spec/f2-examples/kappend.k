// A rule whose right side concatenates two K sequences: kompile writes `append(K1, K2)`, K's
// `append` of the prelude's module KSEQ, whose equations the text states there.
module KAPPEND-SYNTAX
  imports K-EQUAL-SYNTAX
  syntax KItem ::= run(K, K) [symbol(run)] | a() [symbol(a)] | b() [symbol(b)]
endmodule

module KAPPEND
  imports KAPPEND-SYNTAX
  configuration <k> $PGM:K </k>
  rule [go]: <k> run(K1, K2) => K1 ~> K2 </k>
endmodule
