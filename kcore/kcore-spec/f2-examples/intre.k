// The library sort Int declared again in a user module (`syntax Int`, as wasm's
// wasm-data/int-type.k does): kompile then writes Int's hooked-sort declaration without a place.
// The reader recognises UNSIGNED-INT-SYNTAX by the declaration's content, so Int is a library
// sort below the user's `Num`.
module INTRE-SYNTAX
  imports INT-SYNTAX
  syntax Int
  syntax Num ::= Int | neg(Int) [symbol(neg)]
  syntax Cmd ::= go(Num) [symbol(go)] | done(Num) [symbol(done)]
endmodule

module INTRE
  imports INTRE-SYNTAX
  imports INT
  configuration <k> $PGM:Cmd </k>
  rule [go]: <k> go(N:Int) => done(neg(N)) </k>
endmodule
