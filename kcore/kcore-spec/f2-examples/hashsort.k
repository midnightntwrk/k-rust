// A token sort whose name begins with `#` (as wasm's `syntax #Layout [token]`): kompile declares no
// projection `project:#Tok` for it.
module HASHSORT-SYNTAX
  imports INT-SYNTAX
  syntax #Tok [token]
  syntax Exp ::= Int | tok(#Tok) [symbol(tok)]
endmodule

module HASHSORT
  imports HASHSORT-SYNTAX
  imports INT
  configuration <k> $PGM:Exp </k>
  rule <k> 1 => 0 ... </k>
endmodule
