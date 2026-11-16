// The program variable in a cell other than `<k>`, and no `<k>` cell: `configuration <T> $PGM:Pgm
// </T>`. The rule rewrites the cell's content.
module PGMT-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int) [symbol(go)] | done(Int) [symbol(done)]
endmodule

module PGMT
  imports PGMT-SYNTAX
  imports INT
  configuration <T> $PGM:Pgm </T>
  rule <T> go(I) => done(I +Int 1) </T>
endmodule
