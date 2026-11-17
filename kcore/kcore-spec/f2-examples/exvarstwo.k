module E3-VARS-TWO
  imports INT
  syntax Exp ::= c() [symbol(c)] | d(Int, Int) [symbol(d)]
  rule <k> c() => d(?Y:Int, ?Z:Int) ... </k>
endmodule
