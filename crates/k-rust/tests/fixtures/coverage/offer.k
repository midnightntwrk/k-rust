module OFFER-SYNTAX
  imports INT-SYNTAX
  imports LIST
  syntax Op ::= pa(Int) [symbol(pa)] | pb(Int) [symbol(pb)] | pc(Int) [symbol(pc)]
              | pd(Int) [symbol(pd)] | pe(Int) [symbol(pe)] | pn(Int) [symbol(pn)]
              | py(Int) [symbol(py)] | ph(Int) [symbol(ph)] | pk(Int) [symbol(pk)]
              | pz(Int) [symbol(pz)]
  syntax Prog ::= "halt" [symbol(halt)] | "fault" [symbol(fault)]
                | seq(Op, Prog) [symbol(seq)] | val(Int) [symbol(val)]
                | seqf(Int, Prog) [symbol(seqf)] | lst(List) [symbol(lst)]
                | seqz(Int, Prog) [symbol(seqz)] | seqy(Int, Int, Prog) [symbol(seqy)]
endmodule

module OFFER
  imports OFFER-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports MAP
  imports LIST
  imports K-EQUAL
  configuration <k> $PGM:Prog </k>

  syntax Int ::= fc(Int) [function, symbol(fc)]
               | fd(Int) [function, symbol(fd)]
               | fe(Int) [function, symbol(fe)]
               | pdk(Int) [function, symbol(pdk)]

  // (a) a lower priority group below the productive one.
  rule [aHigh]:  seq(pa(_), _) => halt
  rule [aLow]:   seq(pa(_), _) => fault [priority(60)]
  // (b) an owise rule behind a productive default rule.
  rule [bMain]:  seq(pb(_), _) => halt
  rule [bOw]:    seq(pb(_), _) => fault [owise]
  // (c) two equations of one group, both matching: the first tried applies.
  rule [c]:      seq(pc(A), _) => val(fc(A))
  rule [fc1]:    fc(X) => X requires X >=Int 0
  rule [fc2]:    fc(X) => X requires X >=Int 1
  // (d) an owise equation behind an applied equation, and behind one that does not match.
  rule [d]:      seq(pd(A), _) => val(fd(A))
  rule [fd1]:    fd(0) => 1
  rule [fdOw]:   fd(_) => 2 [owise]
  // (e) a concrete equation set aside on a symbolic argument, a lower group following.
  rule [e]:      seq(pe(A), _) => val(fe(A))
  rule [feC]:    fe(X) => X [concrete]
  rule [feOw]:   fe(_) => 0 [owise, concrete]
  // (f) a rule whose left-hand side matches no state any program here reaches.
  rule [never]:  seq(pn(_), _) => halt
  // Under strategy any, the later rule of the productive priority.
  rule [yA]:     seq(py(_), _) => halt
  rule [yB]:     seq(py(_), _) => fault
  // (h) a fresh name, an implementation-chosen value and its diagnostic, with competitors.
  rule [hFresh]: seq(ph(_), P) => seqf(!_N:Int, P)
  rule [hLow]:   seq(ph(_), _) => fault [priority(60)]
  rule [hKeys]:  seqf(N, _) => lst(keys_list(N |-> 1 (N +Int 1) |-> 2))
  rule [hOw]:    seqf(_, _) => fault [owise]
  // (k) an equation only the definedness decision of an operand `#if` does not evaluate
  // selects among: the priority-60 one is never tried.
  rule [k]:      seq(pk(A), _) => val(#if A >=Int 0 #then A #else pdk(A) #fi)
  rule [pdk50]:  pdk(I) => 0 requires I >Int 0 [priority(50)]
  rule [pdk60]:  pdk(I) => I /Int 0 [priority(60)]
  // Two symbolic steps, the first with a competitor below it and the second introducing an
  // existential, on a state whose variables are spelled like the rules' `X` and `?_Y`.
  rule [z1]:     seq(pz(X), P) => seqz(X, P)
  rule [zLow]:   seq(pz(X), _) => seqz(X, fault) [priority(60)]
  rule [z2]:     seqz(X, P) => seqy(X, ?_Y:Int, P)
endmodule
