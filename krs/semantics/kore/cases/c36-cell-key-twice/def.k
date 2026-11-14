// Two instances of one key in a cell collection (multiplicity="*", type="Map"): adding an
// instance whose key is present has an undefined result (Map concatenation is undefined on a
// common key), so that path has no final configuration; a rule that matches any instance gives
// one successor for each instance.
module CASE-SYNTAX
  imports INT-SYNTAX
  syntax Cmd ::= new(Int, Int) | "pick"
  syntax Cmds ::= Cmd ";" Cmds | "end" | got(Int, Int) | alt(Cmds, Cmds)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  configuration <t> <k> $PGM:Cmds </k> <accts> <acct multiplicity="*" type="Map"> <id> 0 </id> <bal> 0 </bal> </acct> </accts> </t>
  rule <k> alt(P, _) => P </k>
  rule <k> alt(_, P) => P </k>
  rule <k> new(I, B) ; P => P </k> <accts> ... (.Bag => <acct> <id> I </id> <bal> B </bal> </acct>) </accts>
  rule <k> pick ; _ => got(I, B) </k> <acct> <id> I </id> <bal> B </bal> </acct>
endmodule
