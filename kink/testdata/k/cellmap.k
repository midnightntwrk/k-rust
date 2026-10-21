// CS-15 spike: a kompile-generated cell map in the final configuration.
module CELLMAP-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= open(Int, Int) [symbol(open)]
                | forge(Int, Int) [symbol(forge)]
                | seq(Prog, Prog) [symbol(seq)]
endmodule

module CELLMAP
  imports CELLMAP-SYNTAX
  imports INT
  configuration <k> $PGM:Prog </k>
                <accts>
                  <acct multiplicity="*" type="Map">
                    <id> 0 </id>
                    <bal> 0 </bal>
                  </acct>
                </accts>

  rule [seq]: <k> seq(P, Q) => P ~> Q ... </k>
  rule [open]: <k> open(I, B) => .K ... </k>
               <accts> ( .Bag => <acct> <id> I </id> <bal> B </bal> </acct> ) ... </accts>
endmodule
