// The instances of a type="List" cell collection keep their order, and a rule states the
// position of an instance it writes only among the items written side by side in one cell body,
// which come first, followed by the rest of the list that the cell's ... stands for, wherever that
// ... is written (docs/compatibility.md#cells-written-inside-another-cell).
// mk adds an instance at the front. get writes one instance without its position, so it reads the
// front instance. last, dropLast and mkLast write a leading ... before the instance; that ... is
// the same rest of the list, so they too read, remove and add at the front.
module LIST-CELL-POSITIONS-SYNTAX
  imports INT-SYNTAX
  syntax Cmd ::= mk(Int, Int) | get(Int) | mkLast(Int, Int) | last() | dropLast()
  syntax Pgm ::= Cmd | Cmd ";" Pgm
endmodule

module LIST-CELL-POSITIONS
  imports LIST-CELL-POSITIONS-SYNTAX
  imports INT
  imports LIST
  configuration
    <T>
      <k> $PGM:Pgm </k>
      <rs> <r multiplicity="*" type="List"> <rid> 0 </rid> <v> 0 </v> </r> </rs>
      <out> .List </out>
    </T>

  rule <k> C:Cmd ; P:Pgm => C ~> P ... </k>
  rule <k> mk(I, V) => .K ... </k> <rs> (.Bag => <r> <rid> I </rid> <v> V </v> </r>) ... </rs>
  rule <k> mkLast(I, V) => .K ... </k> <rs> ... (.Bag => <r> <rid> I </rid> <v> V </v> </r>) </rs>
  rule <k> get(I) => .K ... </k> <r> <rid> I </rid> <v> V </v> </r> <out> ... .List => ListItem(V) </out>
  rule <k> last() => .K ... </k> <rs> ... <r> <rid> I </rid> ... </r> </rs> <out> ... .List => ListItem(I) </out>
  rule <k> dropLast() => .K ... </k> <rs> ... (<r> <rid> I </rid> ... </r> => .Bag) </rs> <out> ... .List => ListItem(I) </out>
endmodule
