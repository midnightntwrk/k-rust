module CRYPTO-EXECUTION
  imports BYTES

  syntax Bytes ::= "Keccak256raw" "(" Bytes ")"
    [function, hook(KRYPTO.keccak256raw)]
  syntax Input ::= Bytes

  configuration <k> $PGM:Input </k>
endmodule
