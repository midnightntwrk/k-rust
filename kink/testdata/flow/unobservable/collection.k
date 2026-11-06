// Flow fixture: an unobservable cell <tmp> and a compared cell <val> inside the instances of the
// `*` cell <thread>, a Map keyed by <id>. The projection leaves <tmp> out of each instance and
// compares the threads by key and <val>; `spawn(I)` starts the thread keyed I with <val> and
// <tmp> I.
module COLLECTION-SYNTAX
  imports INT-SYNTAX
  syntax Stmt ::= "emit" "(" Int ")" [symbol(emit)]
                | "spawn" "(" Int ")" [symbol(spawn)]
endmodule

module COLLECTION
  imports COLLECTION-SYNTAX
  imports INT
  configuration <k> $PGM:Stmt </k> <out> 0 </out>
                <threads> <thread multiplicity="*" type="Map"> <id> 0 </id> <val> 0 </val> <tmp unobservable=""> 0 </tmp> </thread> </threads>

  rule [emit]: <k> emit(I:Int) => .K ... </k> <out> O => O +Int I </out>
  rule [spawn]: <k> spawn(I:Int) => .K ... </k>
                <threads> ( .Bag => <thread> <id> I </id> <val> I </val> <tmp> I </tmp> </thread> ) ... </threads>
endmodule
