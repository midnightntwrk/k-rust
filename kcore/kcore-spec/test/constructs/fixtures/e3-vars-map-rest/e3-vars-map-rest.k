module E3-VARS-MAP-REST
  imports INT
  imports MAP
  syntax Exp ::= go() [symbol(go)]
  configuration <k> $PGM:Exp </k> <m> .Map </m>
  rule <k> go() => .K ... </k> <m> M => (?K:Int |-> 0) M </m>
endmodule
