module E3-VARS-BOOL
  imports BOOL
  syntax Exp ::= c() [symbol(c)] | d(Bool) [symbol(d)]
  rule <k> c() => d(?Z:Bool) </k>
endmodule
