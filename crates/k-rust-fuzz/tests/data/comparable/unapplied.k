// An undefined step in a definition without data (kink27 FUZZ-UNDEF-P3 review, finding 1).
//
// The equation `ListItem(1) => ListItem(2)` states two `List` constructions equal; the evaluator
// never applies it (its full critical-pair check reports a decided precondition row), so the
// definition has no data: constructors and collections are not shown to be distinct normal forms.
// `go(1)` reaches `chk(ListItem(1))`; the evaluator refutes `two` by matching `ListItem(1)`
// against `ListItem(2)`, applies `other` and takes an undefined step (`1 /Int 0`). Under the
// equation's reading `chk(ListItem(1))` is `chk(ListItem(2))`, and `two` gives the defined end
// `<k> .K </k> <out> 0 </out>`; under the reading where `List` is the builtin model the definition
// is inconsistent. Under neither is the run's set of ends empty, so the undefined step does not
// make the run comparable.

module UC-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int) [symbol(go)]
endmodule

module UC
  imports UC-SYNTAX
  imports INT
  imports LIST
  syntax KItem ::= chk(List) [symbol(chk)]
  rule ListItem(1) => ListItem(2)
  configuration <k> $PGM:Pgm </k> <out> 0 </out>
  rule [go]:    <k> go(N) => chk(ListItem(N)) </k>
  rule [two]:   <k> chk(ListItem(2)) => .K </k> [priority(10)]
  rule [other]: <k> chk(_) => .K </k> <out> _ => 1 /Int 0 </out> [priority(50)]
endmodule
