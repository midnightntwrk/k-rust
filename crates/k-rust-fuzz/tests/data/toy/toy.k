// One module, as many small definitions are written: the syntax module is the main module, so
// the program grammar sees DOMAINS' builtin operations over `K` (`size(Map)`, `K ==K K`). The
// record sort `Tx` is data and the program sort `Pgm` is not (FZ-02 review 2, NI-1).

module TOY
  imports DOMAINS

  syntax Pgm ::= "send" Int  [symbol(send)]
  syntax Tx  ::= tx(Int, Int) [symbol(tx)]

  configuration <k> $PGM:Pgm </k> <tx> $TX:Tx </tx>

  rule <k> send _:Int => .K ... </k>
endmodule
