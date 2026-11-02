// User lists in their program spelling (krs-unparse unit-test oracle): one sort per list shape,
// each at a call form, beside the productions that read their text otherwise.
module LISTS-SYNTAX
  imports INT-SYNTAX
  syntax Ints ::= List{Int, ","} [symbol(intsCons), terminator-symbol(intsNil)]
  syntax Gaps ::= List{Int, ""} [symbol(gapsCons), terminator-symbol(gapsNil)]
  syntax Alts ::= NeList{Int, "|"} [symbol(altsCons), terminator-symbol(altsNil)]
  syntax Rows ::= List{Ints, ";"} [symbol(rowsCons), terminator-symbol(rowsNil)]
  syntax Bands ::= NeList{Ints, ";"} [symbol(bandsCons), terminator-symbol(bandsNil)]
  syntax W ::= Ints [symbol(wrap), format(%1)]
  syntax Ws ::= List{W, ";"} [symbol(wsCons), terminator-symbol(wsNil)]
  syntax Seq ::= Ints | Gaps
  syntax Exp ::= Val | "tick" [symbol(tick)]
  syntax Val ::= Int
  syntax Exps ::= List{Exp, ","} [symbol(expsCons), terminator-symbol(expsNil), overload(expsCons)]
  syntax Vals ::= List{Val, ","} [symbol(valsCons), terminator-symbol(valsNil), overload(expsCons)]
  syntax Exps ::= Vals
  syntax Stmt ::= "ints" "(" Ints ")" [symbol(ints)]
                | "f" "(" Ints ")" [symbol(call)]
                | "f" "(" ")" [symbol(callNone)]
                | "two" Ints Ints [symbol(two)]
                | "pair" "(" Ints "," Ints ")" [symbol(pair)]
                | "cnt" "(" Ints "," Int ")" [symbol(cnt)]
                | "gaps" "(" Gaps ")" [symbol(gaps)]
                | "juxt" Gaps Gaps [symbol(juxt)]
                | "rows" "(" Rows ")" [symbol(rows)]
                | "bands" "(" Bands ")" [symbol(bands)]
                | "alts" "(" Alts ")" [symbol(alts)]
                | "ws" "(" Ws ")" [symbol(ws)]
                | "seq" "(" Seq ")" [symbol(seq)]
                | "exps" "(" Exps ")" [symbol(exps)]
endmodule

module LISTS
  imports LISTS-SYNTAX
  imports INT
  configuration <k> $PGM:Stmt </k> <m> .Map </m>
endmodule
