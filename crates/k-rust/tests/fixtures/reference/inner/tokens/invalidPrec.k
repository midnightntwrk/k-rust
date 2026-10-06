// Both productions in one module view: one lexeme with two precedences. The upstream
// checks/invalidPrec.k declares only Foo, in a module that imports nothing; Int's lexeme reaches
// that main module only through modules compilation adds (docs/compatibility.md, "Grammar scope
// of token precedence"). Declared inline so this focused rule-grammar test has no prelude setup.
module MAIN
  syntax Foo ::= r"[0-9]+" [token]
  syntax Int ::= r"[0-9]+" [prec(2), token]
endmodule
