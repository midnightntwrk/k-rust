module E1-PARAM
  imports BOOL
  syntax {S} S ::= pick(Bool, S, S)         [function, symbol(pick)]
  syntax {S, T} Bool ::= same(S, T)         [function, symbol(same)]
  rule pick(true, A, _) => A
  rule pick(false, _, B) => B
  rule same(_, _) => true
endmodule
