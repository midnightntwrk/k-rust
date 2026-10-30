module PRIO-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= Int
endmodule

module PRIO
  imports PRIO-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Pgm </k>

  // A table whose last row has a later priority, as KRS writes a default row: it gives the value
  // only where no earlier row applies.
  syntax Int ::= table(Int) [function, total]
  rule table(0) => 10
  rule table(1) => 11
  rule table(_) => 12 [priority(200)]

  // Two rows of distinct priorities over one argument.
  syntax Int ::= ranked(Int) [function, total]
  rule ranked(0) => 111 [priority(40)]
  rule ranked(_) => 222 [priority(80)]

  // Rows of one priority told apart by bit patterns and a literal, then a default row.
  syntax Int ::= field(Int) [function]
  rule field(X) => 1 requires X >=Int 0 andBool X <Int 256 andBool bitRangeInt(X, 6, 2) ==Int 1
  rule field(226) => 3
  rule field(X) => 2 requires X >=Int 0 andBool X <Int 256 andBool bitRangeInt(X, 6, 2) ==Int 3
    andBool bitRangeInt(X, 0, 3) ==Int 1
  rule field(_) => 0 [priority(200)]

  rule <k> X:Int => table(X) +Int ranked(X) +Int field(X) </k> requires X <Int 1000
endmodule
