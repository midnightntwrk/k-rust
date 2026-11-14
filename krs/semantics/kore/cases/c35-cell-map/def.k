// A cell collection (multiplicity="*", type="Map", keyed by the child cell <id>): a rule adds an
// instance beside the others, a rule removes the instance of a key, and a rule rewrites a child
// of the one instance of a key among three; the instances are created in an order other than
// that of their keys.
module CASE-SYNTAX
  imports INT-SYNTAX
  syntax Cmd ::= new(Int, Int) | del(Int) | inc(Int)
  syntax Cmds ::= Cmd ";" Cmds | "end"
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  configuration <t> <k> $PGM:Cmds </k> <accts> <acct multiplicity="*" type="Map"> <id> 0 </id> <bal> 0 </bal> </acct> </accts> </t>
  rule <k> new(I, B) ; P => P </k> <accts> ... (.Bag => <acct> <id> I </id> <bal> B </bal> </acct>) </accts>
  rule <k> del(I) ; P => P </k> <accts> ... (<acct> <id> I </id> ... </acct> => .Bag) </accts>
  rule <k> inc(I) ; P => P </k> <acct> <id> I </id> <bal> B => B +Int 1 </bal> </acct>
endmodule
