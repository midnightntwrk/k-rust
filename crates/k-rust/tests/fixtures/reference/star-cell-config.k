module STAR-CELL-CONFIG
  imports INT

  syntax Cmd ::= "run"
  configuration
    <top>
      <k> $PGM:Cmd </k>
      <entries>
        <entry multiplicity="*" type="Map">
          <id> 0 </id>
          <value> $VALUE:Int </value>
        </entry>
      </entries>
    </top>
endmodule
