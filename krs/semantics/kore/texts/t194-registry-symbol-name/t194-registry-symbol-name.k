// A constructor of a sort of the text's own declared under the symbol name of INT's _+Int_, with no
// module of INT imported.
module T194-REGISTRY-SYMBOL-NAME-SYNTAX
  syntax Num ::= "z" [symbol(z)] | Num "+Int" Num [symbol(_+Int_)]
  syntax Cmd ::= go(Num) [symbol(go)] | done() [symbol(done)]
endmodule

module T194-REGISTRY-SYMBOL-NAME
  imports T194-REGISTRY-SYMBOL-NAME-SYNTAX
  configuration <k> $PGM:Cmd </k>
  rule [go]: <k> go(z +Int z) => done() </k>
endmodule
