// A token sort of the text with a constructor beside its tokens.
module RDR-TOKEN-CTOR
  imports INT
  syntax Tok ::= r"[a-z]+" [token] | mk(Int) [symbol(mk)]
endmodule
