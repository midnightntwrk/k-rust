module LIST-UNIFICATION
  imports BOOL
  imports LIST

  syntax Val ::= "x" | "y" | "z"
               | "success" | "ready"
               | "test1"

  configuration
    <T>
      <k> $PGM:Val </k>
      <a> .List </a>
      <b> .List </b>
    </T>

  rule
    <k> test1 => ready ... </k>
    <a> .List => ListItem(x) ListItem(y) ListItem(z) </a>
    <b> .List => ListItem(x) ListItem(y) ListItem(z) </b>

  rule
    <k> ready => success ... </k>
    <a> L:List </a>
    <b> L </b>
endmodule
