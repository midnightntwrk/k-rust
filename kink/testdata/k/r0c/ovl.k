// Re-pin R0c-fix-3: the R0c-fix-2 review's probe review-probe2/ovl.k, kept as written. An edit of
// the lesser fint reaches the greater fnum through kompile's overload axiom, so fnum's total is
// removed too.
module OVL-SYNTAX
  imports INT-SYNTAX
  syntax Num ::= Int
  syntax Num ::= f(Num) [function, total, overload(f), symbol(fnum)]
  syntax Int ::= f(Int) [function, total, overload(f), symbol(fint)]
  syntax Prog ::= chk(Num) [symbol(chk)] | go(Num) [symbol(go)] | yes() [symbol(yes)] | val(Num) [symbol(val)]
endmodule
module OVL
  imports OVL-SYNTAX
  imports INT
  imports BOOL
  imports K-EQUAL
  configuration <k> $PGM:Prog </k>
  rule [fint]: f(I:Int) => 10 /Int (I +Int 1)
  rule [chk]: <k> chk(N:Num) => yes() </k> requires f(N) ==K 10
  rule [go]: <k> go(N:Num) => val(f(N)) </k>
endmodule
