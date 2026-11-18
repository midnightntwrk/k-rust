// KVAR (substitution.md): the hooked token sort KVar (`syntax KVar [token, hook(KVAR.KVar)]`), read
// as a token sort of the definition's own (Parse.ownTokenHookedSort?); its hooked function
// String2KVar (hook STRING.string2token) read as a parameter symbol of the definition's own; the
// private function freshKVar with its equation, which the text holds; a literal of KVar.
// fixture.toml params records `kcore sem-fields`'s parameter lines.
requires "substitution.md"
module E6-PARAM-KVAR
  imports KVAR
  imports INT
  imports STRING
  syntax KItem ::= go(Int, String) [symbol(go)]
  rule <k> go(1, S:String) => String2KVar(S) ... </k>
  rule <k> go(2, _) => #token("x", "KVar") ... </k>
endmodule
