// Set patterns without concatenation: `SetItem(P)` alone in a left side (as the corpus's
// symbolic-collection-frames), and a cell set's element alone (`<task>` of multiplicity `*`, type
// `Set`). Each denotes the one-element sets of P's values, so its match is unique.
module SETITEM-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= "go" [symbol(go)] | got(Int) [symbol(got)] | "clear" [symbol(clear)]
               | "done" [symbol(done)] | "finish" [symbol(finish)]
endmodule

module SETITEM
  imports SETITEM-SYNTAX
  imports INT
  imports SET
  configuration <k> $PGM:Pgm </k> <s> SetItem(1) </s>
                <tasks> <task multiplicity="*" type="Set"> <id> 0 </id> </task> </tasks>
  rule [take]: <k> go => got(X) </k> <s> SetItem(X:Int) => .Set </s>
  rule [clear]: <k> clear => done </k> <s> SetItem(1) => .Set </s>
  rule [finish]: <k> finish => got(I) </k> <tasks> <task> <id> I </id> </task> => .Bag </tasks>
endmodule
