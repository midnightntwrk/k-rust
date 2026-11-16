// A function whose result sort is K.
module KRESFN-SYNTAX
  imports INT-SYNTAX
  syntax K ::= f(Int) [function, symbol(f)]
  syntax Cmd ::= run(Int) [symbol(run)]
endmodule

module KRESFN
  imports KRESFN-SYNTAX
  imports INT
  configuration <k> $PGM:Cmd </k>
  rule f(X) => X
  rule [go]: <k> run(N) => f(N) </k>
endmodule
