// Format codes, assoc dedent, and colours (krs-unparse unit-test oracle; outputs recorded from Java K 7.1.337 krun).
module FORMATS-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= Stmt
               | Stmt Pgm [symbol(stmts), format(%1%n%2)]
  syntax Stmt ::= "{" Pgm "}" [symbol(block), format(%1%i%n%2%d%n%3)]
                | "say" Int ";" [symbol(say), colors(red, yellow), format(%1 %2%3)]
                | "pct" Int ";" [symbol(pct), format(%1 %%%2 %x%3)]
                | "sp" Int ";" [symbol(sp), format(%1% %2%3)]
                | "note" Int ";" [symbol(note), color(magenta), format(%c//note%r%n%1 %2%3)]
                | "tint" Int ";" [symbol(tint), color(NoSuchColour)]
                | "list" Lst ";" [symbol(listStmt)]
  syntax Lst ::= Int
               | Lst "," Lst [symbol(lst), left, assoc, format(%i%1%2%n%3%d)]
endmodule

module FORMATS
  imports FORMATS-SYNTAX
  imports INT
  configuration <k color="green"> $PGM:Pgm </k>
endmodule
