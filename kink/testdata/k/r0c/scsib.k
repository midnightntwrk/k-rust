// Re-pin R0c-fix-2: the R0c-fix-1 review's probe review-probe/scsib.k, kept as written.
module SCSIB-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Prog ::= sib(Int) [symbol(sib)] | res(Bool) [symbol(res)] | other() [symbol(other)]
endmodule
module SCSIB
  imports SCSIB-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Prog </k>
  rule [siba]: <k> sib(I) => res(false andBool 10 /Int (I -Int 1) >Int 0) </k>
  rule [sibb]: <k> sib(_) => other() </k>
endmodule
