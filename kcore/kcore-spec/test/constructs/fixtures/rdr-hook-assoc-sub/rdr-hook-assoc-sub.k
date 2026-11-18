// A hooked function of the text (hook INT.sub) with no equation, declared assoc: the associativity
// axiom of a symbol whose hook's function, integer subtraction, is not associative
// (rdr-hook-assoc is the same text with hook INT.add, whose function is). The law is read and owed
// like any function's; here it is false at values.
module RDR-HOOK-ASSOC-SUB
  imports INT
  imports BOOL
  syntax Int ::= minus(Int, Int) [function, total, hook(INT.sub), assoc, symbol(minus)]
endmodule
