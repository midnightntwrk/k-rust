// A probe for collection patterns (PatVal.coll, KcoreSpec/Evaluation.lean): rules whose left-hand
// sides match a list (`ListItem(X) L`, `L ListItem(X)`) and a cell map (`<acct> <id> I </id> ... </acct>`
// inside `<accts>`, a cell of multiplicity `*`).
// Compiled to colls.kore by findings/work/p42/colls-kore.sh.
module COLLS
  imports INT
  imports LIST
  syntax Op ::= "pop" [symbol(pop)] | "drop" [symbol(drop)] | bump(Int) [symbol(bump)]
  syntax Ops ::= Op | Op ";" Ops [symbol(seq)]
  configuration <k> $PGM:Ops </k> <stack> ListItem(1) ListItem(2) </stack> <sum> 0 </sum>
                <accts> <acct multiplicity="*" type="Map"> <id> 0 </id> <bal> 0 </bal> </acct> </accts>
  rule <k> O:Op ; Os:Ops => O ~> Os ... </k>
  rule <k> pop => .K ... </k> <stack> ListItem(X:Int) L:List => L </stack> <sum> S => S +Int X </sum>
  rule <k> drop => .K ... </k> <stack> L:List ListItem(_) => L </stack>
  rule <k> bump(I) => .K ... </k> <acct> <id> I </id> <bal> B => B +Int 1 </bal> </acct>
endmodule
