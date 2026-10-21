// TB-02: exact matching versus equivalent equality-guarded rules, with owise fallbacks.
module TB02INPUT-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  imports STRING-SYNTAX
  imports BYTES-SYNTAX
  imports LIST
  imports MAP
  imports SET
  syntax Prog ::= boolCheck(Bool) [symbol(boolCheck)]
                | stringCheck(String) [symbol(stringCheck)]
                | bytesCheck(Bytes) [symbol(bytesCheck)]
                | listCheck(List) [symbol(listCheck)]
                | mapCheck(Map) [symbol(mapCheck)]
                | setCheck(Set) [symbol(setCheck)]
                | done(Int) [symbol(done)]
endmodule
module TB02INPUT
  imports TB02INPUT-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports STRING
  imports BYTES
  imports LIST
  imports MAP
  imports SET
  configuration <k> .K </k>
  rule [bool]: boolCheck(true) => done(7)
  rule [boolow]: boolCheck(_) => done(0) [owise]
  rule [string]: stringCheck("A") => done(7)
  rule [stringow]: stringCheck(_) => done(0) [owise]
  rule [bytes]: bytesCheck(b"A") => done(7)
  rule [bytesow]: bytesCheck(_) => done(0) [owise]
  rule [list]: listCheck(ListItem(1) ListItem(2)) => done(7)
  rule [listow]: listCheck(_) => done(0) [owise]
  rule [map]: mapCheck((1 |-> 2) (3 |-> 4)) => done(7)
  rule [mapow]: mapCheck(_) => done(0) [owise]
  rule [set]: setCheck(SetItem(1) SetItem(2)) => done(7)
  rule [setow]: setCheck(_) => done(0) [owise]
endmodule

// TB-02: user-defined totality and positive partial predicates on a stuck constructor state.
module TB02PRED-SYNTAX
  imports INT-SYNTAX
  syntax Int ::= totalInput(Int) [function, total, symbol(totalInput)]
               | partialInput(Int) [function, symbol(partialInput)]
  syntax Prog ::= pair(Int, Int) [symbol(pair)]
endmodule
module TB02PRED
  imports TB02PRED-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  configuration <k> .K </k>
  rule [totalInput]: totalInput(X) => 7
  rule [partialInput]: partialInput(0) => 7
endmodule
