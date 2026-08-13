module STDIN-STREAM-TEST
  imports LIST
  imports INT

  syntax Command ::= "read" [symbol(read)]

  configuration
    <top>
      <k> read </k>
      <input stream="stdin"> .List </input>
    </top>

  rule
    <k> read => Value ... </k>
    <input> ListItem(Value:Int) => .List ... </input>
endmodule
