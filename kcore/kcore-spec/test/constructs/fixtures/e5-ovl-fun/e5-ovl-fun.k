module E5-OVL-FUN
  imports INT
  syntax Exp ::= Int
  syntax Exp ::= Exp "+" Exp [symbol(plusExp), overload(plus)]
  syntax Int ::= Int "+" Int [function, symbol(plusInt), overload(plus)]
  rule I1:Int + I2:Int => I1 +Int I2
endmodule
