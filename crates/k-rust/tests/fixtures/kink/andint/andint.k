module ANDINT
  imports INT
  imports BOOL
  syntax KItem ::= stay(Int) [symbol(stay)] | "done" [symbol(done)]
  configuration <k> $PGM:KItem </k>
endmodule
