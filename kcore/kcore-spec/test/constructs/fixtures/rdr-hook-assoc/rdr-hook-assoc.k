// A hooked function of the text (hook INT.add) with no equation, declared assoc: kompile writes the
// associativity axiom of a symbol that is neither a collection's concatenation nor a function the
// definition reads with clauses (c3-hook-only without assoc reads cleanly).
module RDR-HOOK-ASSOC
  imports INT
  imports BOOL
  syntax Int ::= plus(Int, Int) [function, total, hook(INT.add), assoc, symbol(plus)]
endmodule
