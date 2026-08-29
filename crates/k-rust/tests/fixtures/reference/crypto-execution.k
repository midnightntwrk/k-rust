module CRYPTO-EXECUTION
  imports BYTES
  imports INT
  imports STRING

  syntax Bytes ::= "Keccak256raw" "(" Bytes ")"
    [function, hook(KRYPTO.keccak256raw)]
  syntax String ::= "Sha256" "(" Bytes ")"
    [function, hook(KRYPTO.sha256)]
  syntax Bytes ::= "EcdsaRecover" "(" Bytes "," Int "," Bytes "," Bytes ")"
    [function, hook(KRYPTO.ecdsaRecover)]
  syntax Input ::= Bytes | String

  configuration <k> $PGM:Input </k>
endmodule
