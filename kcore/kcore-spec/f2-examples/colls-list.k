// A probe for list patterns (PatVal.coll, KcoreSpec/Evaluation.lean): rules whose left-hand sides
// match a list from the front (`ListItem(X) L`) and from the back (`L ListItem(_)`). Tied by the
// kernel in test/CollsList.lean. Compiled to colls-list.kore by findings/work/p42/colls-kore.sh.
module COLLS-LIST
  imports INT
  imports LIST
  syntax Op ::= "pop" [symbol(pop)] | "drop" [symbol(drop)]
  syntax Ops ::= Op | Op ";" Ops [symbol(seq)]
  configuration <k> $PGM:Ops </k> <stack> ListItem(1) ListItem(2) </stack> <sum> 0 </sum>
  rule <k> O:Op ; Os:Ops => O ~> Os ... </k>
  rule <k> pop => .K ... </k> <stack> ListItem(X:Int) L:List => L </stack> <sum> S => S +Int X </sum>
  rule <k> drop => .K ... </k> <stack> L:List ListItem(_) => L </stack>
endmodule
