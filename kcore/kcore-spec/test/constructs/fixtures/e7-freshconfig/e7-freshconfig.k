module E7-FRESHCONFIG
  imports INT
  syntax Exp ::= a() [symbol(a)]
  configuration <k> $PGM:Exp </k> <id> !N:Int </id>
endmodule
