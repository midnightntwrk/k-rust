module TEST
  imports INT
  imports LIST
  imports BOOL
  imports K-EQUAL
  configuration <t>
    <k> $PGM:K </k>
    <accounts> <account multiplicity="*" type="Map"> <id> 0 </id> <bal> 0 </bal> </account> </accounts>
    <tags> <tag multiplicity="*" type="Set"> 0 </tag> </tags>
    <queue> <item multiplicity="*" type="List"> 0 </item> </queue>
    <saved> .List </saved>
    <one> <inner> 0 </inner> </one>
    <optc> <maybe multiplicity="?"> 0 </maybe> </optc>
    <two> <acc2 multiplicity="*" type="Map"> <key2> 0 </key2> </acc2> <cnt> 0 </cnt> </two>
    <pair> <l> 0 </l> <r> 0 </r> </pair>
  </t>
  syntax Bag
  syntax KItem ::= "clear" | "save" | "restore" | box(AccountsCell) | "clearTags" | "clearQueue" | "keepQueue"
                 | "keepAccounts" | "keepOne" | "dropMaybe" | "castBag" | "oneAccount" | "mapAnnotated"
                 | "mixed" | "two" | "pair" | "pairRead" | "zeroOne" | "anonymous" | "checked" | "tested"
                 | "castFragment" | "let" | "go" | fooK(K) | fooBag(Bag)
  syntax Bool ::= pb(Bag) [function]
  rule pb(_) => true
  rule [clear]: <k> clear => .K ... </k> <accounts> _ => .Bag </accounts>
  rule [save]: <k> save => .K ... </k> <accounts> A </accounts> <saved> .List => ListItem(box(<accounts> A </accounts>)) ... </saved>
  rule [restore]: <k> restore => .K ... </k> <accounts> _ => A </accounts> <saved> ListItem(box(<accounts> A </accounts>)) => .List ... </saved>
  rule [clear-tags]: <k> clearTags => .K ... </k> <tags> _ => .Bag </tags>
  rule [clear-queue]: <k> clearQueue => .K ... </k> <queue> _ => .Bag </queue>
  rule [keep-queue]: <k> keepQueue => .K ... </k> <queue> Q </queue> <saved> _ => ListItem(Q) </saved>
  rule [keep-accounts]: <k> keepAccounts => fooK(A) ... </k> <accounts> A </accounts>
  rule [keep-one]: <k> keepOne => fooK(X) ... </k> <one> X </one>
  rule [drop-maybe]: <k> dropMaybe => .K ... </k> <optc> X => .Bag </optc>
  rule [cast-bag]: <k> castBag => .K ... </k> <accounts> X:Bag => .Bag </accounts>
  rule [one-account]: <k> oneAccount => .K ... </k> <accounts> X:AccountCell </accounts>
  rule [map-annotated]: <k> mapAnnotated => fooK(A:AccountCellMap) ... </k> <accounts> A </accounts>
  rule [mixed]: <k> mixed => .K ... </k> <accounts> A <account> <id> 1 </id> ... </account> </accounts>
  rule [two]: <k> two => fooK(A) ... </k> <two> A <cnt> C </cnt> </two> requires C >Int 0
  rule [pair]: <k> pair => fooK(P) ... </k> <pair> P </pair>
  rule [pair-read]: <k> pairRead => fooK(P) ... </k> <pair> <l> 1 </l> P </pair>
  rule [zero-one]: <k> zeroOne => fooK(X) ... </k> <one> <inner> 1 </inner> X </one>
  rule [anonymous]: <k> anonymous => .K ... </k> <pair> _ </pair> <accounts> _ </accounts> <tags> _ </tags>
  rule [checked]: <k> checked => .K ... </k> <accounts> A </accounts> requires fooK(A) ==K fooK(A)
  rule [tested]: <k> tested => .K ... </k> <accounts> A </accounts> requires isAccountsCellFragment(A)
  rule [cast-fragment]: <k> castFragment => fooK(A:AccountsCellFragment) ... </k> <accounts> A </accounts>
  rule [let]: <k> let => #let Y = fooK(A) #in Y ... </k> <accounts> A </accounts>
  rule [boxed]: box(<accounts> A </accounts>) => fooK(A)
endmodule
