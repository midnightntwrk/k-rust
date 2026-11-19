// hybrid(Int) on a strict production: K's user manual (hybrid attribute) says it generates
// isInt(pair(E1, E2)) => true requires isInt(E1) andBool isInt(E2), an equation of the predicate of
// the registry sort Int.
module E2-HYBRID-REGISTRY
  imports INT
  imports BOOL
  syntax Exp ::= Int
               | pair(Exp, Exp) [symbol(pair), strict, hybrid(Int)]
  syntax KResult ::= Int
endmodule
