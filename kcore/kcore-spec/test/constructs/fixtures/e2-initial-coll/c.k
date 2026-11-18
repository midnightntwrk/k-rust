module C
  imports INT
  imports MAP
  imports SET
  imports LIST
  syntax Exp ::= a() [symbol(a)]
  configuration <t>
                  <k> $PGM:Exp </k>
                  <ts> <th multiplicity="*" type="Set"> <id> 0 </id> </th> </ts>
                  <ms> <mt multiplicity="*" type="Map"> <key> 0 </key> <v> 0 </v> </mt> </ms>
                  <ls> <lt multiplicity="*" type="List" initial=""> 0 </lt> </ls>
                </t>
endmodule
