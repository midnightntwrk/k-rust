module VOID
  imports INT
  imports BOOL
  syntax Void
  syntax KItem ::= hold(Void) [symbol(hold)] | stay(Int) [symbol(stay)] | "done" [symbol(done)]
  configuration <k> $PGM:KItem </k>
endmodule
