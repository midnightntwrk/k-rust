module E3-VARS-BOTTOM
  imports INT
  syntax Exp ::= c() [symbol(c)] | d(Int) [symbol(d)]
  rule <k> c() => d(?Z:Int) #And #Bottom </k>
endmodule
