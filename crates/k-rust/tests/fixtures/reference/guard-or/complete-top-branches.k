module WEM15-COMPLETE-TOP-BRANCHES
  imports INT
  imports BOOL
  syntax Foo ::= "a" | "b" | "c"
  configuration
    <top>
      <k> $PGM:Foo </k>
      <x> 0 </x>
    </top>
  rule
    <top>
      <k> a => c </k>
      <x> 0 </x>
    </top>
    #Or
    <top>
      <k> b => c </k>
      <x> 0 </x>
    </top>
endmodule
