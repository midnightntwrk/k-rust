// Re-pin R0b (decision 4, finding C-09): a well-sorted List whose role symbols carry no role
// hook. k-rust 501f18b9's loader allows it (R1-R4: a role's hook, if it has one, is its own), so it
// compiles; kink's census rule C refuses it, because only a role with its role hook over a sort
// with the namespace's sort hook is a natural collection (R0a: b1coll.k and t13role.k, the earlier
// rule C fixtures, are now refused by k-rust itself).
module HOOKLESSROLE-SYNTAX
  imports INT-SYNTAX
  syntax LI [hook(LIST.List)]
  syntax LI ::= LI LI [function, total, left, assoc, symbol(_LI_), element(LIItem), unit(.LI)]
  syntax LI ::= ".LI" [function, total, symbol(.LI)]
  syntax LI ::= LIItem(Int) [function, total, symbol(LIItem)]
  syntax Prog ::= start(Int) [symbol(start)]
                | done(LI) [symbol(done)]
endmodule
module HOOKLESSROLE
  imports HOOKLESSROLE-SYNTAX
  imports INT
  configuration <k> $PGM:Prog </k>
  rule [start]: <k> start(I) => done(LIItem(I)) </k>
endmodule
