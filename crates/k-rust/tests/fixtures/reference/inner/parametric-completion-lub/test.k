// Pinned K rejects this rule while completing #fun3 because the two parser-layer #KToken
// children have sort KBott, whose filtered upper bounds have no unique admissible minimum.
module PARAMETRIC-COMPLETION-LUB
  imports INT

  syntax Int ::= trigger() [function]
  rule trigger() => #fun(#token("pattern", "Missing") => 0)(#token("argument", "Missing"))
endmodule
