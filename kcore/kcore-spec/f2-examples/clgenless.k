// A clause whose `requires` holds a variable of a sort the text leaves unconfined (S has the
// generator `c(Empty)` over a sort without a value), beside an `[owise]` clause, as CX-F 5 (with an
// argument: kompile refuses the nullary `f()` of that text, fixture e2-clause-genless). The
// condition `isC(H)` is closed; no value of S satisfies it, and the text does not say that no
// element does: the clause's `CondDecided` is owed and open (test/B1bClauses.lean).
module CLGENLESS
  imports INT
  imports BOOL
  syntax Empty
  syntax S ::= "a" [symbol(a)] | c(Empty) [symbol(c)]
  syntax Bool ::= isC(S) [function, total, symbol(isC)]
  rule isC(c(_)) => true
  rule isC(_) => false [owise]
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(_) => 1 requires isC(H:S) [unboundVariables(H)]
  rule f(_) => 0 [owise]
  syntax KItem ::= "go" [symbol(go)]
  rule <k> go => f(0) </k>
endmodule
