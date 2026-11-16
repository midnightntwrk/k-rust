// User token sorts. `Name` is declared a token sort (`syntax Name [token]`, as wasm's
// `IdentifierToken`), and below a sort with a constructor (`Ident ::= Name`, as wasm's
// `IdentifierToken < Identifier`); `Tag` is a token sort K infers from its token production alone.
// Their values are their literals; the rule moves a `Name` literal out of its injection.
module USERTOK-SYNTAX
  syntax Name [token]
  syntax Name ::= r"[a-z][a-z0-9]*" [token]
  syntax Tag ::= r"[A-Z][a-z]*" [token]
  syntax Ident ::= Name | anon() [symbol(anon)]
  syntax Cmd ::= go(Ident) [symbol(go)] | done(Name) [symbol(done)] | tag(Tag) [symbol(tag)]
endmodule

module USERTOK
  imports USERTOK-SYNTAX
  configuration <k> $PGM:Cmd </k>
  rule [go]: <k> go(N:Name) => done(N) </k>
endmodule
