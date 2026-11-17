module E3-VARS-ENS-FREE
  imports INT
  imports BOOL
  syntax Exp ::= c() [symbol(c)]
  rule <k> c() => c() </k> ensures ?Z ==Int 0
endmodule
