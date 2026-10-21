// Re-pin R0b (finding C-10): an equation rooted at the List element role symbol, which k-rust
// never applies and reports as IndexedAt(List) (k-rust tests/collection_leaf_contract.rs).
module ROLEROOTED-SYNTAX
  imports INT-SYNTAX
  imports LIST
  syntax Prog ::= start(Int) [symbol(start)]
                | done(List) [symbol(done)]
endmodule
module ROLEROOTED
  imports ROLEROOTED-SYNTAX
  imports INT
  imports LIST
  configuration <k> $PGM:Prog </k>
  rule [start]: <k> start(I) => done(ListItem(I)) </k>
  rule [roleeq]: ListItem(1) => ListItem(2)
endmodule
