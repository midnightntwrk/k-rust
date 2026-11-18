module E5-OVL-HOOK
  imports INT
  syntax Exp ::= Int
  syntax Exp ::= Exp "+" Exp [symbol(plusExp), overload(plus)]
  syntax Int ::= Int "+" Int [function, total, hook(INT.add), symbol(plusInt), overload(plus)]
endmodule
