module TEST
  imports INT
  imports LIST
  configuration <t>
    <k> $PGM:K </k>
    <accounts> <account multiplicity="*" type="Map"> <id> 0 </id> <bal> 0 </bal> </account> </accounts>
    <tags> <tag multiplicity="*" type="Set"> 0 </tag> </tags>
    <queue> <item multiplicity="*" type="List"> 0 </item> </queue>
    <saved> .List </saved>
  </t>
  syntax KItem ::= "clear" | "save" | "restore" | box(AccountsCell) | "clearTags" | "clearQueue" | "keepQueue"
  rule [clear]: <k> clear => .K ... </k> <accounts> _ => .Bag </accounts>
  rule [save]: <k> save => .K ... </k> <accounts> A </accounts> <saved> .List => ListItem(box(<accounts> A </accounts>)) ... </saved>
  rule [restore]: <k> restore => .K ... </k> <accounts> _ => A </accounts> <saved> ListItem(box(<accounts> A </accounts>)) => .List ... </saved>
  rule [clear-tags]: <k> clearTags => .K ... </k> <tags> _ => .Bag </tags>
  rule [clear-queue]: <k> clearQueue => .K ... </k> <queue> _ => .Bag </queue>
  rule [keep-queue]: <k> keepQueue => .K ... </k> <queue> Q </queue> <saved> _ => ListItem(Q) </saved>
endmodule
