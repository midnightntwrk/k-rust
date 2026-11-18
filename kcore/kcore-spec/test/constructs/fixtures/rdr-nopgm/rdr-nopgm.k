// A configuration with no configuration variable: the <k> cell's initial content is a constant.
module RDR-NOPGM-SYNTAX
  syntax Foo ::= "foo" [symbol(foo)]
endmodule
module RDR-NOPGM
  imports RDR-NOPGM-SYNTAX
  configuration <k> foo </k>
endmodule
