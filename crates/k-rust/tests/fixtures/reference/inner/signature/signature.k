// Adapted from k-distribution/tests/regression-new/checks/signature.k.
// Terminals replace token productions so this fixture isolates visibility.
module A [private]
  syntax Foo ::= foo()
  syntax Foo ::= bam() [public]
  syntax Foo ::= fu() [private]
  syntax Foo ::= "bar" [public]
  syntax Foo ::= "baz"
endmodule

module B
  imports private A
  syntax Bar ::= a() [public] | b() [private]
endmodule

module C
  imports B
  rule foo() => .K
  rule bam() => .K
  rule fu() => .K
  rule bar => .K
  rule baz => .K
  rule a() => .K
  rule b() => .K
endmodule

module SIGNATURE
  imports C
endmodule
