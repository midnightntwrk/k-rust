module E3-VARS-REQ-ONLY
  imports INT
  syntax Exp ::= c() [symbol(c)] | d(Int) [symbol(d)]
  rule <k> c() => d(0) </k> requires ?Z >Int 0
endmodule
