module NATP
  imports INT
  imports BOOL
  syntax Nat ::= "z" [symbol(z)] | s(Nat) [symbol(s)]
  syntax KItem ::= stay(Int) [symbol(stay)]
  configuration <k> $PGM:KItem </k>
endmodule
