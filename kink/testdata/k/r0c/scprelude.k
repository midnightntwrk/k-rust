// A definition with one constructor and no rule of its own, over the builtin modules a
// definition imports (DOMAINS, and the domains it leaves out): no rewrite rule of them
// depends on the short-circuit reading, and one equation does (isInfinite's).
module SCPRELUDE-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Prog ::= go(Int, String) [symbol(go)]
endmodule
module SCPRELUDE
  imports SCPRELUDE-SYNTAX
  imports DOMAINS
  imports BYTES
  imports FLOAT
  imports ARRAY
  imports RANGEMAP
  imports K-REFLECTION
  imports STRING-BUFFER
  configuration <k> $PGM:Prog </k>
endmodule
