module T39-CELL-COLLECTION-MAP
  imports INT
  syntax Exp ::= get(Int) | r(Int)
  configuration <k> $PGM:Exp </k>
                <accts> <acct multiplicity="*" type="Map"> <id> 0 </id> <bal> 0 </bal> </acct> </accts>
  rule <k> get(I) => r(B) ... </k> <acct> <id> I </id> <bal> B </bal> </acct>
endmodule
