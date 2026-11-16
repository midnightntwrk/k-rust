// A rule that rewrites inside a list, as K's regression test macro-rewrite: `:` is a macro for
// `ListItem(I) L`, so `(5 => 6) : _` is `ListItem(5) _ => ListItem(6) _`, whose top symbol `_List_`
// (LIST's concatenation, a function) makes kompile write it as an equation of `_List_`. The
// registry interprets `_List_` as list concatenation; the equation states more of it (two distinct
// lists are one), and no function of the definition has it as a clause: it is not accounted for,
// named as an equation of a symbol the registry interprets.
module REGEQ-SYNTAX
  imports INT-SYNTAX
  imports LIST
endmodule

module REGEQ
  imports REGEQ-SYNTAX
  imports INT
  imports BOOL
  syntax List ::= Int ":" List [macro]
  rule I : L => ListItem(I) L
  rule (5 => 6) : _
endmodule
