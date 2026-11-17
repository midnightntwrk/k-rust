module FOO
  imports INT
  syntax Int ::= foo(Int) [function]
  rule foo(0) => 0
  rule foo(_) => 1 [priority(200)]
endmodule
