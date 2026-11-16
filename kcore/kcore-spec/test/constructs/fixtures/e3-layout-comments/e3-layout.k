/* a block comment */
module E3-LAYOUT // a line comment
  imports INT
	syntax Exp ::= a() [symbol(a)] | b() [symbol(b)]   /* tab, spaces */
  rule <k> a()   =>   b() ... </k>
endmodule
