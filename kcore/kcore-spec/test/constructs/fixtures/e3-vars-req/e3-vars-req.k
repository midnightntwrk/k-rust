module E3-VARS-REQ
  imports INT
  syntax Exp ::= c() [symbol(c)] | d(Int) [symbol(d)]
  rule <k> c() => d(?Z:Int) </k> requires ?Z >Int 0
endmodule
