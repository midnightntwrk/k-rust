// KEVM's vendored krypto.md declares KRYPTO.keccak256, absent from the builtins.
module T13IMPLEMENTED-SYNTAX
  imports INT-SYNTAX
  imports STRING-SYNTAX
  imports BYTES-SYNTAX
  syntax Prog ::= start(Int) [symbol(start)] | chk(String) [symbol(chk)] | done(Int) [symbol(done)]
endmodule
module T13IMPLEMENTED
  imports T13IMPLEMENTED-SYNTAX
  imports BASIC-K
  imports INT
  imports STRING
  imports BYTES
  configuration <k> .K </k>
  syntax String ::= keccak(Bytes) [function, hook(KRYPTO.keccak256), symbol(keccak)]
  rule [start]: start(I) => chk(keccak(Int2Bytes(1, I, BE)))
  rule [hit]: chk("") => done(1)
  rule [ow]: chk(_) => done(0) [owise]
endmodule
