// The configuration variable $PGM in a cell other than <k>.
module T225-PGM-OUTSIDE-K
  imports INT
  syntax Pgm ::= "p" [symbol(p)]
  configuration <k> .K </k> <q> $PGM:Pgm </q>
endmodule
