// A user hooked sort whose hook is a library sort's and not a collection's.
module MYINT-SYNTAX
  imports INT-SYNTAX
  syntax MyInt [hook(INT.Int)]
  syntax Cmd ::= run(MyInt) [symbol(run)] | done() [symbol(done)]
endmodule

module MYINT
  imports MYINT-SYNTAX
  configuration <k> $PGM:Cmd </k>
  rule [go]: <k> run(_) => done() </k>
endmodule
