module E3-WITHCONFIG
  imports INT
  syntax Exp ::= a() [symbol(a)] | b(Int) [symbol(b)]
  syntax Int ::= cur() [function, symbol(cur)]
  configuration <k> $PGM:Exp </k> <s> 0 </s>
  rule [[ cur() => N ]] <s> N </s>
  rule <k> a() => b(cur()) ... </k>
endmodule
