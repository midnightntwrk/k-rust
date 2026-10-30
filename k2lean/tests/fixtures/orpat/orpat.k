module ORPAT-SYNTAX
  imports INT-SYNTAX
  syntax Op ::= inc(Int) | dec(Int) | neg(Int) | "nop"
  syntax Pgm ::= Op | "halt"
endmodule

module ORPAT
  imports ORPAT-SYNTAX
  imports INT
  configuration <k> $PGM:Pgm </k> <acc> 0 </acc>

  // An or-pattern in an equation's argument, beside a literal row and an owise row.
  syntax Int ::= cost(Op) [function, total]
  rule cost(inc(_) #Or dec(_)) => 1
  rule cost(nop) => 0
  rule cost(_) => 2 [owise]

  // An or-pattern in a rewrite rule, each alternative binding I.
  rule <k> (inc(I) #Or dec(I)) => halt </k> <acc> A => A +Int I </acc> [label(step)]
  rule <k> neg(I) => halt </k> <acc> A => A -Int I </acc>
endmodule
