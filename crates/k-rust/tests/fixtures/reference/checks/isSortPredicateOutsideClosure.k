// reference: k/result/bin/kompile --backend haskell isSortPredicateOutsideClosure.k
// Accepted (exit 0): the auto-imported prelude's RANGEMAP declares sort Range, but no module of
// the main closure imports it and its own import closure carries rules, so
// DefinitionParsing.parseDefinitionAndResolveBubbles drops it before Kompile.checkIsSortPredicates.
// This is the pinned MIR semantics shape (rt/data.md:698, `syntax Bool ::= isRange(Value)`).
module ISSORTPREDICATEOUTSIDECLOSURE
  imports DOMAINS
  syntax Value ::= Foo(List)
  syntax Bool ::= isRange(Value) [function, total]
endmodule
