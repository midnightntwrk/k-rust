// CS-15: a Panopticon-shaped definition (an <env> Map, a strict let, an outcome cell).
module COLLENV-SYNTAX
  imports INT-SYNTAX
  imports ID-SYNTAX
  syntax Exp ::= Int | Id
  syntax Pgm ::= Exp
               | "let" Id "=" Exp ";" Pgm [strict(2)]
endmodule

module COLLENV
  imports COLLENV-SYNTAX
  imports INT
  imports MAP
  syntax KResult ::= Int
  syntax Outcome ::= "running" | returned(Int)
  configuration <k> $PGM:Pgm </k> <env> .Map </env> <outcome> running </outcome>

  rule [variable]: <k> X:Id => V ... </k> <env> ... X |-> V ... </env>
  rule [declaration]: <k> let X = V:Int ; P:Pgm => P ... </k> <env> Rho => Rho [ X <- V ] </env>
  rule [returned]: <k> V:Int => .K </k> <outcome> running => returned(V) </outcome>
endmodule
