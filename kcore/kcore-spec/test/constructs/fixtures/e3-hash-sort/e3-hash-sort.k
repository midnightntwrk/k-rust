// A token sort whose name begins with `#` (as wasm's `syntax #Layout [token]`), the text of
// f2-examples/hashsort.k: KItem's no-junk sentence lists no `inj{#Tok, KItem}` and no subsort
// sentence puts `#Tok` below KItem, while the equations of `is#Tok` apply `inj{#Tok, KItem}`.
module E3-HASH-SORT-SYNTAX
  imports INT-SYNTAX
  syntax #Tok [token]
  syntax Exp ::= Int | tok(#Tok) [symbol(tok)]
endmodule

module E3-HASH-SORT
  imports E3-HASH-SORT-SYNTAX
  imports INT
  configuration <k> $PGM:Exp </k>
  rule <k> 1 => 0 ... </k>
endmodule
