// /Int truncates toward zero and %Int takes the sign of the dividend, for each sign of the operands.
module CASE-SYNTAX
  imports INT-SYNTAX
  syntax S ::= go(Int, Int) | r(Int, Int, Int, Int, Int, Int, Int, Int)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  configuration <k> $PGM:S </k>
  rule <k> go(X, Y) => r(X /Int Y, X %Int Y, (0 -Int X) /Int Y, (0 -Int X) %Int Y,
                         X /Int (0 -Int Y), X %Int (0 -Int Y), (0 -Int X) /Int (0 -Int Y), (0 -Int X) %Int (0 -Int Y)) </k>
endmodule
