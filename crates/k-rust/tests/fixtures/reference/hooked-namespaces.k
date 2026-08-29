module HOOKED-NAMESPACES
  imports BYTES
  imports INT
  imports STRING

  syntax Bytes ::= "KeccakRaw" "(" Bytes ")"
    [function, hook(KRYPTO.keccak256raw)]
  syntax String ::= "Sha256" "(" Bytes ")"
    [function, hook(HASH.sha256)]
  syntax Bytes ::= "Recover" "(" Bytes "," Int "," Bytes "," Bytes ")"
    [function, hook(SECP256K1.ecdsaRecover)]
endmodule
