module ASSOC-STRICT
  imports INT
  imports BOOL
  syntax Exp ::= Int
               | Exp "+" Exp [left, seqstrict, symbol(plus)]
               | Exp "*" Exp [right, strict, symbol(times)]
               | Exp "-" Exp [non-assoc, strict(2), symbol(minus), prefer, avoid]
  syntax KResult ::= Int
  configuration <k> $PGM:Exp </k> <n> 0 </n>
  rule I1:Int + I2:Int => I1 +Int I2
  rule I1:Int * I2:Int => I1 *Int I2
  rule I1:Int - I2:Int => I1 -Int I2
endmodule
