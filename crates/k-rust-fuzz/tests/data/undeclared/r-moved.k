// The baseline with `syntax Pgm ::= done(Int)` moved from `R-SYNTAX` to `R` (FZ-ENGINE-R4 review
// B1): a refactoring with no semantic change, which renames the production's generated KORE
// label. Each side's end `<k> done(N) </k>` names a symbol the other definition does not
// declare, so the ends cannot be compared and no case may kill.

module R-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= go(Int)  [symbol(go)]
endmodule

module R
  imports R-SYNTAX
  imports INT

  syntax Pgm ::= done(Int)

  configuration <k> $PGM:Pgm </k>

  rule <k> go(N) => done(N) </k>
endmodule
