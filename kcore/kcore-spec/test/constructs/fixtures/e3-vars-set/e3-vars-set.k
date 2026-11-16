module E3-VARS-SET
  imports INT
  imports SET
  syntax Exp ::= go() [symbol(go)]
  configuration <k> $PGM:Exp </k> <s> .Set </s>
  rule <k> go() => .K ... </k> <s> S => SetItem(?V:Int) S </s>
endmodule
