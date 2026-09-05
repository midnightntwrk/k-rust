module CONFIG-VAR-CAST
  imports INT-SYNTAX

  syntax KItem ::= "a" | "b"

  configuration
    <test>
      <k> $PGM </k>
      <n> $N:Int </n>
    </test>

  rule <k> a => b </k>
endmodule
