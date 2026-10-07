// VI-T12 probes: definition-computed hooked values against non-canonical literals.
// Every row is a start symbol taking a canonical Int, a check symbol with a literal
// rule (done(7)) and an owise rule (done(0)).
module T12PROBE-SYNTAX
  imports INT-SYNTAX
  imports FLOAT-SYNTAX
  imports STRING-SYNTAX
  imports BYTES-SYNTAX
  syntax Prog ::= done(Int) [symbol(done)]
  // Float rows
  syntax Prog ::= f1s(Int) [symbol(f1s)] | f1c(Float) [symbol(f1c)]
  syntax Prog ::= f2s(Int) [symbol(f2s)] | f2c(Float) [symbol(f2c)]
  syntax Prog ::= f3s(Int) [symbol(f3s)] | f3c(Float) [symbol(f3c)]
  syntax Prog ::= f4s(Int) [symbol(f4s)] | f4c(Float) [symbol(f4c)]
  syntax Prog ::= f5s(Int) [symbol(f5s)] | f5c(Float) [symbol(f5c)]
  syntax Prog ::= f6s(Int) [symbol(f6s)] | f6c(Float) [symbol(f6c)]
  syntax Prog ::= f7s(Int) [symbol(f7s)] | f7c(Float) [symbol(f7c)]
  syntax Prog ::= f8s(Int) [symbol(f8s)] | f8c(Float) [symbol(f8c)]
  syntax Prog ::= f9s(Int) [symbol(f9s)] | f9c(Float) [symbol(f9c)]
  syntax Prog ::= f10s(Int) [symbol(f10s)] | f10c(Float) [symbol(f10c)]
  syntax Prog ::= f11s(Int) [symbol(f11s)] | f11c(Float) [symbol(f11c)]
  syntax Prog ::= f12s(Int) [symbol(f12s)] | f12c(Float) [symbol(f12c)]
  syntax Prog ::= f13s(Int) [symbol(f13s)] | f13c(Float) [symbol(f13c)]
  syntax Prog ::= f14s(Int) [symbol(f14s)] | f14c(Float) [symbol(f14c)]
  syntax Prog ::= f15s(Int) [symbol(f15s)] | f15c(Float) [symbol(f15c)]
  syntax Prog ::= f16s(Int) [symbol(f16s)] | f16c(Float) [symbol(f16c)]
  // String rows
  syntax Prog ::= s1s(Int) [symbol(s1s)] | s1c(String) [symbol(s1c)]
  syntax Prog ::= s2s(Int) [symbol(s2s)] | s2c(String) [symbol(s2c)]
  syntax Prog ::= s3s(Int) [symbol(s3s)] | s3c(String) [symbol(s3c)]
  syntax Prog ::= s4s(Int) [symbol(s4s)] | s4c(String) [symbol(s4c)]
  syntax Prog ::= s5s(Int) [symbol(s5s)] | s5c(String) [symbol(s5c)]
  syntax Prog ::= s6s(Int) [symbol(s6s)] | s6c(String) [symbol(s6c)]
  syntax Prog ::= s7s(Int) [symbol(s7s)] | s7c(String) [symbol(s7c)]
  syntax Prog ::= s8s(Int) [symbol(s8s)] | s8c(String) [symbol(s8c)]
  syntax Prog ::= s9s(Int) [symbol(s9s)] | s9c(String) [symbol(s9c)]
  // Bytes rows
  syntax Prog ::= b1s(Int) [symbol(b1s)] | b1c(Bytes) [symbol(b1c)]
  syntax Prog ::= b2s(Int) [symbol(b2s)] | b2c(Bytes) [symbol(b2c)]
  syntax Prog ::= b3s(Int) [symbol(b3s)] | b3c(Bytes) [symbol(b3c)]
  // Int control
  syntax Prog ::= i1s(Int) [symbol(i1s)] | i1c(Int) [symbol(i1c)]
endmodule
module T12PROBE
  imports T12PROBE-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports FLOAT
  imports STRING
  imports BYTES
  imports K-EQUAL
  configuration <k> .K </k>

  // F1: lhs 1.0e0 vs Int2Float(1)
  rule [f1s]: f1s(I) => f1c(Int2Float(I, 53, 11))
  rule [f1p]: f1c(1.0e0) => done(7)
  rule [f1o]: f1c(_) => done(0) [owise]
  // F2: lhs 1.0p53x11 vs Int2Float(1)
  rule [f2s]: f2s(I) => f2c(Int2Float(I, 53, 11))
  rule [f2p]: f2c(1.0p53x11) => done(7)
  rule [f2o]: f2c(_) => done(0) [owise]
  // F3: lhs canonical spelling vs Int2Float(1) (control)
  rule [f3s]: f3s(I) => f3c(Int2Float(I, 53, 11))
  rule [f3p]: f3c(1.0000000000000000e+00p53x11) => done(7)
  rule [f3o]: f3c(_) => done(0) [owise]
  // F4: lhs 2.0 vs Int2Float(1) +Float Int2Float(1)
  rule [f4s]: f4s(I) => f4c(Int2Float(I, 53, 11) +Float Int2Float(I, 53, 11))
  rule [f4p]: f4c(2.0) => done(7)
  rule [f4o]: f4c(_) => done(0) [owise]
  // F5: lhs 0.1 vs Int2Float(1) /Float Int2Float(1 +Int 9)
  rule [f5s]: f5s(I) => f5c(Int2Float(I, 53, 11) /Float Int2Float(I +Int 9, 53, 11))
  rule [f5p]: f5c(0.1) => done(7)
  rule [f5o]: f5c(_) => done(0) [owise]
  // F6: lhs 0.0 vs Int2Float(0)
  rule [f6s]: f6s(I) => f6c(Int2Float(I, 53, 11))
  rule [f6p]: f6c(0.0) => done(7)
  rule [f6o]: f6c(_) => done(0) [owise]
  // F7: lhs -0.0 vs --Float Int2Float(0)
  rule [f7s]: f7s(I) => f7c(--Float Int2Float(I, 53, 11))
  rule [f7p]: f7c(-0.0) => done(7)
  rule [f7o]: f7c(_) => done(0) [owise]
  // F8: lhs NaN vs Int2Float(0) /Float Int2Float(0)
  rule [f8s]: f8s(I) => f8c(Int2Float(I, 53, 11) /Float Int2Float(I, 53, 11))
  rule [f8p]: f8c(NaN) => done(7)
  rule [f8o]: f8c(_) => done(0) [owise]
  // F9: lhs Infinity vs Int2Float(1) /Float Int2Float(1 -Int 1)
  rule [f9s]: f9s(I) => f9c(Int2Float(I, 53, 11) /Float Int2Float(I -Int 1, 53, 11))
  rule [f9p]: f9c(Infinity) => done(7)
  rule [f9o]: f9c(_) => done(0) [owise]
  // F10: requires F ==K 1.0 vs Int2Float(1)
  rule [f10s]: f10s(I) => f10c(Int2Float(I, 53, 11))
  rule [f10p]: f10c(F) => done(7) requires F ==K 1.0
  rule [f10o]: f10c(_) => done(0) [owise]
  // F11: requires F ==Float 1.0 vs Int2Float(1)
  rule [f11s]: f11s(I) => f11c(Int2Float(I, 53, 11))
  rule [f11p]: f11c(F) => done(7) requires F ==Float 1.0
  rule [f11o]: f11c(_) => done(0) [owise]
  // F12: literal in a function equation's rhs, compared with ==K
  syntax Float ::= f12one() [function, total, symbol(f12one)]
  rule [f12e]: f12one() => 1.0
  rule [f12s]: f12s(I) => f12c(Int2Float(I, 53, 11))
  rule [f12p]: f12c(F) => done(7) requires F ==K f12one()
  rule [f12o]: f12c(_) => done(0) [owise]
  // F13: literal in a function equation's lhs
  syntax Bool ::= f13is(Float) [function, total, symbol(f13is)]
  rule [f13e]: f13is(1.0) => true
  rule [f13eo]: f13is(_) => false [owise]
  rule [f13s]: f13s(I) => f13c(Int2Float(I, 53, 11))
  rule [f13p]: f13c(F) => done(7) requires f13is(F)
  rule [f13o]: f13c(_) => done(0) [owise]
  // F14: String2Float hook vs lhs 1.0
  rule [f14s]: f14s(I) => f14c(String2Float(Int2String(I) +String ".0"))
  rule [f14p]: f14c(1.0) => done(7)
  rule [f14o]: f14c(_) => done(0) [owise]
  // F15: no hook; rule-literal to rule-literal (spelling mutant on the rhs)
  rule [f15s]: f15s(_) => f15c(1.0)
  rule [f15p]: f15c(1.0) => done(7)
  rule [f15o]: f15c(_) => done(0) [owise]
  // F16: hook consumes a non-canonical rhs literal, compared to lhs literal of same value
  rule [f16s]: f16s(I) => f16c(Int2Float(I, 53, 11) *Float 1.0e0)
  rule [f16p]: f16c(1.0) => done(7)
  rule [f16o]: f16c(_) => done(0) [owise]

  // Value guard used by the String rows' equivalent mutants (equation unchanged).
  syntax Bool ::= streq(String, String) [function, total, symbol(streq)]
  rule [streq]: streq(A, B) => A ==String B
  // S1: lhs "A" vs chrChar(65)
  rule [s1s]: s1s(I) => s1c(chrChar(I))
  rule [s1p]: s1c("A") => done(7)
  rule [s1o]: s1c(_) => done(0) [owise]
  // S2: lhs "\x41" vs chrChar(65)
  rule [s2s]: s2s(I) => s2c(chrChar(I))
  rule [s2p]: s2c("\x41") => done(7)
  rule [s2o]: s2c(_) => done(0) [owise]
  // S3: lhs raw "Ā" (UTF-8 C4 80) vs chrChar(256)
  rule [s3s]: s3s(I) => s3c(chrChar(I))
  rule [s3p]: s3c("Ā") => done(7)
  rule [s3o]: s3c(_) => done(0) [owise]
  // S4: lhs "\n" vs chrChar(10)
  rule [s4s]: s4s(I) => s4c(chrChar(I))
  rule [s4p]: s4c("\n") => done(7)
  rule [s4o]: s4c(_) => done(0) [owise]
  // S5: lhs "\x00" vs chrChar(0)
  rule [s5s]: s5s(I) => s5c(chrChar(I))
  rule [s5p]: s5c("\x00") => done(7)
  rule [s5o]: s5c(_) => done(0) [owise]
  // S6: lhs "a\x31" vs "a" +String Int2String(1)
  rule [s6s]: s6s(I) => s6c("a" +String Int2String(I))
  rule [s6p]: s6c("a\x31") => done(7)
  rule [s6o]: s6c(_) => done(0) [owise]
  // S7: lhs "\x62" vs substrString("abc", 1, 2)
  rule [s7s]: s7s(I) => s7c(substrString("abc", I, I +Int 1))
  rule [s7p]: s7c("\x62") => done(7)
  rule [s7o]: s7c(_) => done(0) [owise]
  // S8: no hook; rule-literal to rule-literal (spelling mutant on the rhs)
  rule [s8s]: s8s(_) => s8c("A")
  rule [s8p]: s8c("A") => done(7)
  rule [s8o]: s8c(_) => done(0) [owise]

  // S9: lhs "\u0100" (escape) vs chrChar(256)
  rule [s9s]: s9s(I) => s9c(chrChar(I))
  rule [s9p]: s9c("\u0100") => done(7)
  rule [s9o]: s9c(_) => done(0) [owise]

  // B1: lhs b"A" vs String2Bytes(chrChar(65))
  rule [b1s]: b1s(I) => b1c(String2Bytes(chrChar(I)))
  rule [b1p]: b1c(b"A") => done(7)
  rule [b1o]: b1c(_) => done(0) [owise]
  // B2: lhs b"\xff" vs Int2Bytes(1, 255, BE)
  rule [b2s]: b2s(I) => b2c(Int2Bytes(1, I, BE))
  rule [b2p]: b2c(b"\xff") => done(7)
  rule [b2o]: b2c(_) => done(0) [owise]
  // Value guards used by the Bytes rows' equivalent mutants (equations unchanged).
  syntax Bool ::= b1guard(Bytes) [function, total, symbol(b1guard)]
  rule [b1g]: b1guard(B) => lengthBytes(B) ==Int 1 andBool Bytes2Int(B, BE, Unsigned) ==Int 65
  syntax Bool ::= b2guard(Bytes) [function, total, symbol(b2guard)]
  rule [b2g]: b2guard(B) => lengthBytes(B) ==Int 1 andBool Bytes2Int(B, BE, Unsigned) ==Int 255
  // B3: no hook; rule-literal to rule-literal (spelling mutant on the rhs)
  rule [b3s]: b3s(_) => b3c(b"A")
  rule [b3p]: b3c(b"A") => done(7)
  rule [b3o]: b3c(_) => done(0) [owise]

  // I1: Int control; rule-literal to rule-literal (spelling mutant on the rhs)
  rule [i1s]: i1s(_) => i1c(1)
  rule [i1p]: i1c(1) => done(7)
  rule [i1o]: i1c(_) => done(0) [owise]
  // Census function-internal routes (V2, V4, V5a, V5b).
  syntax Prog ::= fstart(Int) [symbol(fstart)] | gostart(Int) [symbol(gostart)] | lstart(Int) [symbol(lstart)]
  syntax Int ::= check(Float) [function, total, symbol(check)] | eqk(Float, Float) [function, total, symbol(eqk)]
  rule [cpoint]: check(1.0) => 7
  rule [cow]: check(_) => 0 [owise]
  rule [eqkyes]: eqk(A, B) => 7 requires A ==K B
  rule [eqkno]: eqk(_, _) => 0 [owise]
  rule [fstart]: fstart(I) => done(check(Int2Float(I, 53, 11)))
  rule [gostart]: gostart(I) => done(eqk(Int2Float(I, 53, 11), 1.0))
  rule [lstart]: lstart(_) => done(eqk(1.0, 1.00))
endmodule
