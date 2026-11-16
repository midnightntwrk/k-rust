// A map in a cell, kompiled with `--backend llvm`: the text holds MAP's sentences but not the
// definedness lemma of a map concatenation (`#Ceil(K |-> V Rest)`), a lemma without a place that
// kompile writes from the map's symbols for `--backend haskell`. The lemma is no sentence of MAP's
// file and states nothing the reading reads, so the account does not require it.
module MAPL-SYNTAX
  imports INT-SYNTAX
  syntax Cmd ::= put(Int, Int) [symbol(put)] | done() [symbol(done)]
endmodule

module MAPL
  imports MAPL-SYNTAX
  imports INT
  imports MAP
  configuration <k> $PGM:Cmd </k> <m> .Map </m>
  rule [put]: <k> put(K, V) => done() ... </k> <m> M => M[K <- V] </m>
endmodule
