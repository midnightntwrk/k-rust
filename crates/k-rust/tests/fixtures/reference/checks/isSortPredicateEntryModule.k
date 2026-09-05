// reference: k/result/bin/kompile --backend haskell isSortPredicateEntryModule.k
// Rejected (exit 113, "Syntax declaration conflicts with automatically generated isRange
// predicate."): RANGE-SYNTAX is an entry module whose import closure holds no bubble, so
// parseDefinitionAndResolveBubbles keeps it and its Range generates isRange.
module RANGE-SYNTAX
  syntax Range ::= "range"
endmodule

module ISSORTPREDICATEENTRYMODULE
  imports DOMAINS
  syntax Value ::= Foo(List)
  syntax Bool ::= isRange(Value) [function, total]
endmodule
