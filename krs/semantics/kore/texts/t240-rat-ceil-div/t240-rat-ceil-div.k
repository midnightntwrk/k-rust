// A text that imports RAT. Its module RAT-SYMBOLIC holds the [simplification] sentence
// #Ceil(@R1 /Rat @R2) => {(@R2 =/=Rat 0) #Equals true} #And #Ceil(@R1) #And #Ceil(@R2)
// (rat.md:109-112) beside the four equations of /Rat (rat.md:152-155).
requires "rat.md"
module T240-RAT-CEIL-DIV
  imports RAT
endmodule
