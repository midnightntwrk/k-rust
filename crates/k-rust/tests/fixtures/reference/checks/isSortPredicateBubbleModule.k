// reference: k/result/bin/kompile --backend haskell isSortPredicateBubbleModule.k
// Accepted (exit 0): RANGE-RULES declares sort Range but carries a rule bubble and nothing imports
// it, so it is not an entry module of the parsed definition and its Range never generates isRange.
module RANGE-RULES
  syntax Range ::= "r" | "s"
                 | flip(Range) [function, total]
  rule flip(r) => s
  rule flip(s) => r
endmodule

module ISSORTPREDICATEBUBBLEMODULE
  imports BOOL
  syntax Value ::= "v"
  syntax Bool ::= isRange(Value) [function]
endmodule
