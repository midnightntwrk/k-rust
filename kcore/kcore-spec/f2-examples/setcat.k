// Concatenating set patterns: `SetItem(X) REST` in a left side (as the corpus's
// collection-and-injection-narrowing), a set concatenation on a right side whose parts may share a
// member, and a cell set's element concatenated with the other tasks, updated in place (as the
// corpus's star-cell-heating-set). `_Set_` is the union of two sets with no member in common.
module SETCAT-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= "go" [symbol(go)] | "add" [symbol(add)] | "bump" [symbol(bump)] | "done" [symbol(done)]
endmodule

module SETCAT
  imports SETCAT-SYNTAX
  imports INT
  imports SET
  configuration <k> $PGM:Pgm </k> <s> SetItem(1) SetItem(2) </s>
                <tasks> <task multiplicity="*" type="Set"> <id> 0 </id> </task> </tasks>
  rule [drop]: <k> go => done </k> <s> SetItem(_X) REST => REST </s>
  rule [add]: <k> add => done </k> <s> S => S SetItem(1) </s>
  rule [bump]: <k> bump => done </k> <task> <id> I => I +Int 10 </id> </task>
endmodule
