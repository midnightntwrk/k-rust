module STAR-CELL-MAP-NESTED-SET-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Id ::= "obj" [token]
  syntax Stmt ::= "nop"
                | "decl1" Id Id
                | "decl2" Id Id Id
                | "spawn" "{" Stmt "}"
                | "cast" Id Id
                | Stmt Stmt [left]
endmodule

module STAR-CELL-MAP-NESTED-SET
  imports STAR-CELL-MAP-NESTED-SET-SYNTAX
  imports DOMAINS

  configuration
    <tasks>
      <task multiplicity="*" type="Set">
        <k> $PGM:Stmt </k>
      </task>
    </tasks>
    <classes>
      <classData multiplicity="*" type="Map">
        <className> obj </className>
        <bases> .Set </bases>
      </classData>
    </classes>

  rule <k> S1:Stmt S2:Stmt => S1 ~> S2 ...</k>
  rule <k> nop => .K ...</k>
  rule <k> decl1 C:Id B:Id => .K ...</k>
       <classes> (.Bag => <classData> <className> C </className> <bases> SetItem(B) </bases> </classData>) ...</classes>
  rule <k> decl2 C:Id B1:Id B2:Id => .K ...</k>
       <classes> (.Bag => <classData> <className> C </className> <bases> SetItem(B1) SetItem(B2) </bases> </classData>) ...</classes>
  rule <tasks> <task> <k> spawn { S:Stmt } => .K ...</k> </task>
       (.Bag => <task> <k> S </k> </task>) ...</tasks>
  rule <k> cast C2:Id C1:Id => nop ...</k>
       <className> C1 </className>
       <bases>...SetItem(C2)...</bases>
endmodule
