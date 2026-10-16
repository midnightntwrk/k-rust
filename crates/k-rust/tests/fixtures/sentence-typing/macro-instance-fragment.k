module TEST
  imports INT
  imports LIST
  imports BOOL
  imports K-EQUAL
  configuration <t>
    <k> $PGM:K </k>
    <accounts> <account multiplicity="*" type="Map"> <id> 0 </id> <bal> 0 </bal> </account> </accounts>
    <two> <acc2 multiplicity="*" type="Map"> <id2> 0 </id2> </acc2> <cnt> 0 </cnt> </two>
    <pair> <l> 0 </l> <r> 0 </r> </pair>
  </t>
  syntax Bag
  syntax KItem ::= "a" | "b" | box(AccountsCell) | fooBag(Bag) | fooK(K)
  syntax {S} S ::= m(S) [macro]
  rule m(X:Bag) => X
  rule [r]: <k> a => fooK(m(A)) ... </k> <two> A <cnt> C </cnt> </two>
endmodule
