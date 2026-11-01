// Rules whose conditions read a partial hook outside the inputs its description covers, beside
// controls where the description excludes every value (`L[I]` past the end, `makeList` of a
// negative length, `chrChar` of a non-code-point) or the text states the undefinedness
// (`/Int` by zero, `replaceAtBytes` whose `index + N` is below 0 or past the length, the end
// bound AM-7 reads "valid index" as). Each `yes` rule's condition holds wherever its application is defined
// (`ok` is `total`), so the `owise` rule applies exactly where k-rust takes the application as
// undefined. `gss` reads the value of the `total` `substrString` on an empty range, which its
// description leaves out (it requires `startIndex < endIndex`) and no rule reaches strictly
// inside the string, and `gf`, `grf` and `gfc` search from a start that is no position of the
// haystack (`findChar` through its prelude equations).
// `kprove_proves_nothing_from_a_hook_outside_its_described_domain` in cli.rs.
module OUTSIDE
  imports DOMAINS
  imports BYTES
  syntax Int ::= String2PInt(String) [function, hook(STRING.string2token)]
  syntax Bool ::= ok(KItem) [function, total]
  rule ok(_) => true
  syntax Res ::= "yes" | "no"
  syntax Pgm ::= Res | gu(List, Int) | gr(List, Int) | ga(List, Int) | go(String) | gi(String)
               | gb(String, Int) | gs(Int, Int) | gd(Bytes) | gt(String)
               | ge(List, Int) | gm(Int) | gc(Int) | gz(Int) | gp(Bytes, Int)
               | gss(String, Int) | gf(String, Int) | grf(String, Int) | gfc(String, Int)
  configuration <k> $PGM:Pgm </k>
  rule gu(L, I) => yes requires ok(L [ I <- 0 ])
  rule gu(_, _) => no [owise]
  rule gr(L, I) => yes requires ok(range(L, I, 0))
  rule gr(_, _) => no [owise]
  rule ga(L, I) => yes requires ok(updateList(L, I, ListItem(0)))
  rule ga(_, _) => no [owise]
  rule go(S) => yes requires ok(ordChar(S))
  rule go(_) => no [owise]
  rule gi(S) => yes requires ok(String2Int(S))
  rule gi(_) => no [owise]
  rule gb(S, B) => yes requires ok(String2Base(S, B))
  rule gb(_, _) => no [owise]
  rule gs(I, B) => yes requires ok(Base2String(I, B))
  rule gs(_, _) => no [owise]
  rule gd(B) => yes requires ok(decodeBytes("UTF-8", B))
  rule gd(_) => no [owise]
  rule gt(S) => yes requires ok(String2PInt(S))
  rule gt(_) => no [owise]
  rule ge(L, I) => yes requires ok(L [ I ])
  rule ge(_, _) => no [owise]
  rule gm(N) => yes requires ok(makeList(N, 0))
  rule gm(_) => no [owise]
  rule gc(N) => yes requires ok(chrChar(N))
  rule gc(_) => no [owise]
  rule gz(N) => yes requires ok(1 /Int N)
  rule gz(_) => no [owise]
  rule gp(B, I) => yes requires ok(replaceAtBytes(B, I, b"\x00\x00"))
  rule gp(_, _) => no [owise]
  rule gss(S, I) => yes requires substrString(S, I, I) ==String ""
  rule gss(_, _) => no [owise]
  rule gf(S, I) => yes requires ok(findString(S, "a", I))
  rule gf(_, _) => no [owise]
  rule grf(S, I) => yes requires ok(rfindString(S, "a", I))
  rule grf(_, _) => no [owise]
  rule gfc(S, I) => yes requires ok(findChar(S, "a", I))
  rule gfc(_, _) => no [owise]
endmodule
