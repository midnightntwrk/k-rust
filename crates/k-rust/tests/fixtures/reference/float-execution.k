module FLOAT-EXECUTION
  imports FLOAT
  imports INT

  syntax Float ::= "FloatAdd" "(" Float "," Float ")"
    [function, hook(FLOAT.add)]
                 | "FloatRound" "(" Float "," Int "," Int ")"
    [function, hook(FLOAT.round)]
                 | "FloatMin" "(" Float "," Float ")"
    [function, hook(FLOAT.min)]
                 | "FloatMaxValue" "(" Int "," Int ")"
    [function, hook(FLOAT.maxValue)]
  syntax Bool ::= "FloatEq" "(" Float "," Float ")"
    [function, hook(FLOAT.eq)]
  syntax Int ::= "FloatToInt" "(" Float ")"
    [function, hook(FLOAT.float2int)]
  syntax Input ::= Float | Bool | Int

  configuration <k> $PGM:Input </k>
endmodule
