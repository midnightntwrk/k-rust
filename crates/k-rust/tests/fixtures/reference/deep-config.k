module DEEP-CONFIG
  imports INT

  syntax Cmd ::= "go" | "done"

  configuration
    <top>
      <runtime>
        <machine>
          <control>
            <k> $PGM:Cmd </k>
          </control>
          <settings>
            <env> $ENV:Int </env>
            <mode> $MODE:Int </mode>
          </settings>
          <workers>
            <worker multiplicity="*" type="Map">
              <id> 0 </id>
              <payload> $PGM:Cmd </payload>
            </worker>
          </workers>
        </machine>
      </runtime>
    </top>

  rule <k> go => done </k>
       <env> E => E +Int 1 </env>
       <mode> M => M +Int 2 </mode>
       <worker>... <payload> go => done </payload> ...</worker>
endmodule
