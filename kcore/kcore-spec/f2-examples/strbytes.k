// STRING and BYTES imported as library modules: a rule whose right side computes with String
// operations (`substrString`, `+String`) and Bytes operations (`+Bytes`, `lengthBytes`), whose
// results the kernel computes.
module STRBYTES-SYNTAX
  imports INT-SYNTAX
  imports STRING-SYNTAX
  imports BYTES-SYNTAX
  syntax Cmd ::= go(String, Bytes) [symbol(go)] | done(String, Int) [symbol(done)]
endmodule

module STRBYTES
  imports STRBYTES-SYNTAX
  imports INT
  imports STRING
  imports BYTES
  configuration <k> $PGM:Cmd </k>
  rule [go]: <k> go(S, B) => done(substrString(S, 1, 3) +String "!", lengthBytes(B +Bytes b"\x00\xff")) </k>
endmodule
