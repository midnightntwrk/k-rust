// Re-pin R0b (finding C-10): a simplification rooted at the Set element role symbol, which k-rust
// neither applies nor reports (k-rust tests/collection_leaf_contract.rs): kink scans for it.
module ROLESIMP-SYNTAX
  imports INT-SYNTAX
  imports SET
  syntax Prog ::= start(Int) [symbol(start)]
                | done(Set) [symbol(done)]
endmodule
module ROLESIMP
  imports ROLESIMP-SYNTAX
  imports INT
  imports SET
  configuration <k> $PGM:Prog </k>
  rule [start]: <k> start(I) => done(SetItem(I)) </k>
  rule [rolesimp]: SetItem(1) => SetItem(2) [simplification]
endmodule
