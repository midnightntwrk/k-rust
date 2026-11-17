module E3-VARS-LHS
  imports INT
  syntax Exp ::= c(Int) [symbol(c)] | d(Int) [symbol(d)]
  rule <k> c(?Z:Int) => d(?Z) </k>
endmodule
