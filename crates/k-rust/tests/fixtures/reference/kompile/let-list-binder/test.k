// Reduced from wasm-semantics wasm-data/sparse-bytes.k:82-84 at revision 212271bd434bd402e27c42f6416854342733386d:
// a #let binder whose bound variable also occurs as the element of a user-list concatenation.
module LET-LIST-BINDER
  imports INT
  syntax Item ::= item(Int)
  syntax Chunk ::= chunk(Item)
  syntax Chunks ::= List{Chunk, ""}
  syntax Chunks ::= mk(Item, Int) [function, total]
  rule mk(I, _) => chunk(I) .Chunks
  syntax Chunks ::= concat(Chunks, Int) [function, total]
  rule concat(.Chunks, _) => .Chunks
  rule concat(chunk(I) REST, N) => #let SUB = mk(I, N) #in SUB concat(REST, N -Int 1) requires N >Int 0
  syntax Chunks ::= letInferred(Chunks, Int) [function, total]
  rule letInferred(.Chunks, _) => .Chunks
  rule letInferred(chunk(I) _, N) => #let SUB = mk(I, N) #in letInferred(SUB, N -Int 1) requires N >Int 0
  syntax Chunks ::= funInferred(Chunks, Int) [function, total]
  rule funInferred(.Chunks, _) => .Chunks
  rule funInferred(chunk(I) _, N) => #fun(SUB => funInferred(SUB, N -Int 1))(mk(I, N)) requires N >Int 0
  syntax Chunks ::= letCast(Chunks, Int) [function, total]
  rule letCast(.Chunks, _) => .Chunks
  rule letCast(chunk(I) _, N) => #let SUB:Chunks = mk(I, N) #in letCast(SUB, N -Int 1) requires N >Int 0
endmodule
