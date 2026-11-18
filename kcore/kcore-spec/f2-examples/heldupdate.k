module E3-VARS-UPDATE
  imports INT
  imports MAP
  syntax Exp ::= go() [symbol(go)]
  configuration <k> $PGM:Exp </k> <m> .Map </m>
  rule <k> go() => .K ... </k> <m> M => M [ 0 <- ?V:Int ] [ 0 <- 1 ] </m>
endmodule
