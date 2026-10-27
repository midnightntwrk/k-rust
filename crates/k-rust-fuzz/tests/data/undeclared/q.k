// The baseline with its modules renamed `Q-SYNTAX` and `Q` (FZ-ENGINE-R4 review B1), as a
// mutant written as a file of its own often is: the same definition, whose generated label for
// `done(Int)` names `Q-SYNTAX`, so its ends name a symbol the baseline does not declare.

module Q-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= go(Int)  [symbol(go)]
               | done(Int)
endmodule

module Q
  imports Q-SYNTAX
  imports INT

  configuration <k> $PGM:Pgm </k>

  rule <k> go(N) => done(N) </k>
endmodule
