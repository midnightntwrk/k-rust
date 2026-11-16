// A constructor of a sort of the text's own declared under the KORE name of INT's interpreted hook
// `_+Int_` (symbol(_+Int_), kompile's Lbl'UndsPlus'Int'Unds'), with no module of INT imported.
module E2-REGISTRY-SYMBOL-NAME-SYNTAX
  syntax Num ::= "z" [symbol(z)] | Num "+Int" Num [symbol(_+Int_)]
  syntax Cmd ::= go(Num) [symbol(go)] | done() [symbol(done)]
endmodule

module E2-REGISTRY-SYMBOL-NAME
  imports E2-REGISTRY-SYMBOL-NAME-SYNTAX
  configuration <k> $PGM:Cmd </k>
  rule [go]: <k> go(z +Int z) => done() </k>
endmodule
