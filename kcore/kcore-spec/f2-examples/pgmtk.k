// The program variable in a cell other than `<k>`, a `<k>` cell beside it holding no configuration
// variable: `configuration <T> <k> .K </k> <p> $PGM:Pgm </p> </T>`.
module PGMTK-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int) [symbol(go)] | done(Int) [symbol(done)]
endmodule

module PGMTK
  imports PGMTK-SYNTAX
  imports INT
  configuration <T> <k> .K </k> <p> $PGM:Pgm </p> </T>
  rule <p> go(I) => done(I +Int 1) </p>
endmodule
