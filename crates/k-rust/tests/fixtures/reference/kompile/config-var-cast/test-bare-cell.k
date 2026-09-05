module CONFIG-VAR-INT
  imports INT-SYNTAX
  syntax KItem ::= "a" | "b"
  configuration
    <test>
      <k> $PGM </k>
      <n> $N:Int </n>
      <p> $P </p>
      <m> 0 </m>
    </test>
  syntax Int ::= n() [function]
  rule <k> a => b </k>
endmodule
