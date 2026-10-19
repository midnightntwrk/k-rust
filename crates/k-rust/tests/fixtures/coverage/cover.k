module COVER-SYNTAX
  imports INT-SYNTAX
  syntax Address ::= addr(Int) [symbol(addr)]
  syntax Op ::= load(Address, Int) [symbol(load)]
              | ens(Int) [symbol(ens)]
              | rhsp(Int) [symbol(rhsp)]
              | eqreq(Int) [symbol(eqreq)]
              | rej(Int) [symbol(rej)]
              | ow(Int) [symbol(ow)]
              | ru(Int) [symbol(ru)]
              | rv(Int) [symbol(rv)]
              | pr(Int) [symbol(pr)]
              | hk(Int) [symbol(hk)]
              | d1(Int) [symbol(d1)]
  syntax Prog ::= "halt" [symbol(halt)] | "fault" [symbol(fault)] | "nd" [symbol(nd)]
                | "mid1" [symbol(mid1)] | "mid2" [symbol(mid2)]
                | seq(Op, Prog) [symbol(seq)] | val(Int) [symbol(val)]
endmodule

module COVER
  imports COVER-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports K-EQUAL
  configuration <k> $PGM:Prog </k>

  syntax Int ::= norm(Int) [function, total, symbol(norm)]
               | normE(Int) [function, total, symbol(normE)]
               | part(Int) [function, symbol(part)]
               | inner(Int) [function, total, symbol(inner)]
               | outer(Int) [function, total, symbol(outer)]
               | normR(Int) [function, total, symbol(normR)]
               | owf(Int) [function, total, symbol(owf)]
               | owg(Int) [function, total, symbol(owg)]
               | unused(Int) [function, total, symbol(unused)]
               | pu(Int) [function, symbol(pu)]
               | pv(Int) [function, symbol(pv)]
               | pd(Int) [function, symbol(pd)]

  rule [norm]:    norm(X) => X
  rule [normE]:   normE(X) => X
  rule [part]:    part(X) => X +Int 1 requires X >=Int 0
  rule [inner]:   inner(X) => X
  rule [outer]:   outer(X) => 1 requires inner(X) >=Int 0
  rule [outerow]: outer(_) => 0 [owise]
  rule [normR]:   normR(X) => X
  rule [owg]:     owg(X) => X
  rule [owf1]:    owf(X) => 1 requires owg(X) ==Int 0
  rule [owf2]:    owf(_) => 2 [owise]
  rule [unused]:  unused(X) => X
  rule [puCeil]:  #Ceil(pu(X)) => {(X >=Int 0) #Equals true} [simplification]
  rule [pvCeil]:  #Ceil(pv(_)) => #Top [simplification]
  rule [pdEq]:    pd(X) => X requires X >=Int 0

  rule [load]:    seq(load(addr(A), _), P) => P requires norm(A) ==Int A [preserves-definedness]
  rule [ens]:     seq(ens(A), P) => P ensures normE(A) ==Int A
  rule [rhsp]:    seq(rhsp(A), _) => val(part(A))
  rule [eqreq]:   seq(eqreq(A), _) => val(outer(A))
  rule [rejHigh]: seq(rej(A), _) => fault requires normR(A) <Int 0 [priority(40)]
  rule [rej]:     seq(rej(_), P) => P
  rule [ow]:      seq(ow(A), _) => val(owf(A))
  rule [ru]:      seq(ru(A), _) => val(pu(A))
  rule [rv]:      seq(rv(A), _) => val(pv(A))
  rule [prHigh]:  seq(pr(_), _) => halt [priority(40)]
  rule [prLow]:   seq(pr(_), _) => fault
  rule [hk]:      seq(hk(A), _) => val(A +Int 1)
  rule [d1]:      seq(d1(A), _) => val(#if A >=Int 0 #then A #else pd(A) #fi)
  rule [ndA]:     nd => mid1
  rule [ndB]:     nd => mid2
  rule [mid1]:    mid1 => halt
  rule [mid2]:    mid2 => halt
endmodule
