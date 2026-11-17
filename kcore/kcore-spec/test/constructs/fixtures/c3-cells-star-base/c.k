module C
  imports INT
  imports MAP
  imports SET
  imports LIST
  syntax Exp ::= a() [symbol(a)]
  configuration <t>
                  <k> $PGM:Exp </k>
                  <ts> <th> <id> 0 </id> </th> </ts>
                  <ms> <mt> <key> 0 </key> <v> 0 </v> </mt> </ms>
                  <ls> <lt> 0 </lt> </ls>
                </t>
endmodule
