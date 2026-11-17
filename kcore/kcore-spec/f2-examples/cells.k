module E2-CELLS
  imports INT
  imports MAP
  imports SET
  imports LIST
  syntax Exp ::= a() [symbol(a)]
  configuration <t>
                  <k> $PGM:Exp </k>
                  <one multiplicity="1"> 0 </one>
                  <opt multiplicity="?"> 0 </opt>
                  <ts> <th multiplicity="*" type="Set"> <id> 0 </id> </th> </ts>
                  <ms> <mt multiplicity="*" type="Map"> <key> 0 </key> <v> 0 </v> </mt> </ms>
                  <ls> <lt multiplicity="*" type="List"> 0 </lt> </ls>
                  <exitcode exit=""> 0 </exitcode>
                </t>
  rule <k> a() => .K ... </k> <one> N => N +Int 1 </one>
endmodule
