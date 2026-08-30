module WASM-SHAPED-LISTS
  syntax Type ::= "i32" [symbol(i32)]
  syntax Result ::= "(" "result" Type ")" [symbol(result)]
  syntax Instr ::= "i32.const" Int [symbol(const)]
  syntax Int ::= r"[0-9]+" [token]
  syntax BodyItem ::= Result | Instr
  syntax Stmt ::= Instr
  syntax Results ::= List{Result, ""} [overload(listStmt), symbol(results)]
  syntax Instrs ::= List{Instr, ""} [overload(listStmt), symbol(instrs)]
  syntax BodyItems ::= List{BodyItem, ""} [overload(listStmt), symbol(bodyItems)]
  syntax Stmts ::= List{Stmt, ""} [overload(listStmt), symbol(stmts)]
  syntax Stmts ::= Instrs
  syntax Defn ::= "(" "func" Results Instrs ")" [symbol(func)]
  syntax Item ::= Defn
  syntax Defns ::= List{Defn, ""} [overload(listModule), symbol(defns)]
  syntax Items ::= List{Item, ""} [overload(listModule), symbol(items)]
  syntax Module ::= "(" "module" Defns ")" [symbol(module)]
endmodule
