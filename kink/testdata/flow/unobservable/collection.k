// Flow fixture: an unobservable cell <tmp> inside the instances of the `*` cell <thread>, a Map
// keyed by <id>. The projection leaves <tmp> out of each instance and compares the threads by
// key; `spawn(I)` starts the thread keyed I with <tmp> I.
module COLLECTION-SYNTAX
  imports INT-SYNTAX
  syntax Stmt ::= "emit" "(" Int ")" [symbol(emit)]
                | "spawn" "(" Int ")" [symbol(spawn)]
endmodule

module COLLECTION
  imports COLLECTION-SYNTAX
  imports INT
  configuration <k> $PGM:Stmt </k> <out> 0 </out>
                <threads> <thread multiplicity="*" type="Map"> <id> 0 </id> <tmp unobservable=""> 0 </tmp> </thread> </threads>

  rule [emit]: <k> emit(I:Int) => .K ... </k> <out> O => O +Int I </out>
  rule [spawn]: <k> spawn(I:Int) => .K ... </k>
                <threads> ( .Bag => <thread> <id> I </id> <tmp> I </tmp> </thread> ) ... </threads>
endmodule
