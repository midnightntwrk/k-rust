module E5-OVL-PARAM
  imports INT
  syntax Exp ::= Int
  syntax Exp ::= Exp "+" Exp [symbol(plusExp), overload(plus)]
  syntax Int ::= Int "+" Int [function, symbol(plusInt), overload(plus)]
endmodule
