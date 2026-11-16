// An `[assoc]` function: kompile writes its associativity axiom, of a symbol that is no
// collection's concatenation.
module LAWFN-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= num(Int) [symbol(num)] | Exp "+" Exp [function, assoc, symbol(plus)]
  syntax Cmd ::= run(Exp) [symbol(run)] | done(Exp) [symbol(done)]
endmodule

module LAWFN
  imports LAWFN-SYNTAX
  imports INT
  configuration <k> $PGM:Cmd </k>
  rule num(X) + num(Y) => num(X +Int Y)
  rule [go]: <k> run(E) => done(E) </k>
endmodule
