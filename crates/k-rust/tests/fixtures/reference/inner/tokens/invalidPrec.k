// The reference's checks/invalidPrec.k conflicts with DOMAINS' identical Int lexeme.
// Declare that imported production inline so this focused rule-grammar test has no prelude setup.
module MAIN
  syntax Foo ::= r"[0-9]+" [token]
  syntax Int ::= r"[0-9]+" [prec(2), token]
endmodule
