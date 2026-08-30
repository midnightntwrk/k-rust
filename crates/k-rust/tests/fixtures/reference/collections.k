module LOCAL-COLLECTIONS
  imports INT
  imports MAP
  imports SET
  imports LIST

  syntax Input ::= "mapOps" | "setOps" | "listOps"
                 | MapResult | SetResult | ListResult
  syntax MapResult ::= "mapResult" "(" Map "," KItem "," Int ")"
  syntax SetResult ::= "setResult" "(" Set "," Bool "," Int ")"
  syntax ListResult ::= "listResult" "(" List "," KItem "," Int ")"

  configuration <k> $PGM:Input </k>

  rule <k> mapOps => mapResult(
    updateMap(1 |-> 10 2 |-> 20, 2 |-> 22 3 |-> 30)[1 <- undef],
    (1 |-> 10 2 |-> 20)[2],
    size(1 |-> 10 2 |-> 20))
  </k>
  rule <k> setOps => setResult(
    (SetItem(1) SetItem(2)) |Set (SetItem(2) SetItem(3)),
    2 in (SetItem(1) SetItem(2)),
    size(SetItem(1) SetItem(2)))
  </k>
  rule <k> listOps => listResult(
    ListItem(1) (ListItem(2) ListItem(3)),
    (ListItem(1) ListItem(2))[1],
    size(ListItem(1) ListItem(2)))
  </k>
endmodule
