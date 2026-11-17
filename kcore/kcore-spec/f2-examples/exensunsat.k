module E3-VARS-ENS-UNSAT
  imports INT
  imports BOOL
  syntax Exp ::= c() [symbol(c)] | d(Int) [symbol(d)]
  rule <k> c() => d(?Z:Int) </k> ensures ?Z *Int 2 ==Int 1
endmodule
