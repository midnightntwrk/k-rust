/-
  Agreement at an instance (AgreeInst.lean) on small cores: pairs of equations `fnExclusiveL` leaves
  named and `fnExclusiveI` confirms, a pair it leaves named whose equations disagree, and a
  counter-example for a variant considered and found unsound. Checked by
      lean test/AgreeInst.lean   (LEAN_PATH from `lake env`)

  T is a sort with constructors `c(Int, T)` and `nil`.
  1. `Dw(N, nil #as W) = 1 requires N >Int 0` beside `Dw(N, W) = 2 requires notBool (N >Int 0)`
     (the second's instance at the first's patterns; the `requires` exclude each other).
  2. `Rn(X, Y) = Y` beside `Rn(Y, X) = X` (one equation renamed: the right-hand sides agree).
  3. `Sc(V) = 1 requires notBool (V ==K nil orBool V ==K c(0, nil))` beside `Sc(nil) = 2` (the
     first's instance asserts `nil ==K nil orBool …` false).
  4. `Lf(nil #as X, Y) = 1 requires X =/=K Y` beside `Lf(nil, Y) = 2 requires nil ==K Y` (`=/=K`
     against `==K` of the same terms at the instance).
  `fnExclusiveL` names all four (`in_L`); `fnExclusiveI` names none (`in_I`).
  5. `Ws(nil #as W, N) = c(0, W)` beside `Ws(W, N) = W requires N <Int 0`: named by both
     (`ws_named`); the equations disagree at `(nil, -1)` (`ws_disagree`), as KEVM's
     `WS [ N := W ]` (evm-types.md:275/276) does.
  6. **Counter-example**: `Gm(K |-> V M) = V` beside `Gm(K' |-> V' M') = V'`. A variant that read
     the instance through any head, not only constructors, would accept the pair (the second is the
     first renamed; `instAgreeAny_Gm`); the equations disagree (`gm_disagree`): at the map
     `{1 |-> 1, 2 |-> 2}` the first matches with K = 1 and the second with K' = 2. `fnExclusiveI`
     names Gm (`gm_named`).
  7. Different priorities with an `aside` clause (a `non-executable` equation; FIX-core.agree-aside-prio).
     `Pa(0) = 0` (50) beside `Pa(X) = X` (60, `aside`), the clauses of the fixture
     c3-eq-prio-nonexec: `ClausesAgree` asks nothing of the pair (its premise is false: the
     priorities differ and the `aside` clause is the larger, `pa_premise`), `fnExclusiveL` names
     Pa and `fnExclusiveI` does not (`pa_named`, by `notCompeting`), with or without overloading
     symbols (`pa_pairO`); so the equations agree (`pa_agree`). Known-bad: `Pb(0) = 1` (60) beside
     `Pb(X) = X` (50, `aside`), where the `aside` clause is the smaller: the pair competes
     (`pb_premise`), at 0 the two state 1 and 0, and Pb stays named (`pb_named`, `pb_pairO`);
     `Pc(0) = 1` (60, `aside`) beside `Pc(X) = X` (50, `aside`), both `aside`: competes, named
     (`pc_named`). `notCompeting` is true exactly where the premise is false (`notCompeting_iff`).
-/
import KcoreSpec.AgreeInst
import KcoreSpec.CoreDecide

set_option autoImplicit false

namespace KCore.AgreeInstTest

open KCore KCore.Det

def T0 : Srt := nRegSorts + 2
def cK : Sym := nRegSyms + 52
def cNil : Sym := nRegSyms + 53

def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 50, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 51, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

def core (fns : List Fn) : Semantics where
  lib := { sortsBelowKItem := [Srt.map, Srt.list, Srt.int, Srt.bool] }
  sortNames := []
  symNames := []
  userSorts := cellSorts ++ [T0]
  ctors := cellCtors ++ [⟨cK, [Srt.int, T0], T0⟩, ⟨cNil, [], T0⟩]
  fns := fns
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []

def lit (k : Int) : Term := .dv Srt.int (.int k)
def nil : Term := .app cNil []
def kq (t : Term) : Term := .app kseq [.inj T0 Srt.kitem t, .app dotk []]

def Dw : Sym := nRegSyms + 120
def Rn : Sym := nRegSyms + 121
def Sc : Sym := nRegSyms + 122
def Lf : Sym := nRegSyms + 123
def Ws : Sym := nRegSyms + 124
def Gm : Sym := nRegSyms + 125

def fnDw : Fn := ⟨Dw, [Srt.int, T0], Srt.int,
  [⟨[Srt.int, T0], [.var 0, .as nil 1], some (.app intGt [.var 0, lit 0]), lit 1, none, 50, false, [], .top, .top⟩,
   ⟨[Srt.int, T0], [.var 0, .var 1], some (.app boolNot [.app intGt [.var 0, lit 0]]), lit 2, none, 50, false, [], .top, .top⟩], false⟩

def fnRn : Fn := ⟨Rn, [Srt.int, Srt.int], Srt.int,
  [⟨[Srt.int, Srt.int], [.var 0, .var 1], none, .var 1, none, 50, false, [], .top, .top⟩,
   ⟨[Srt.int, Srt.int], [.var 1, .var 0], none, .var 0, none, 50, false, [], .top, .top⟩], false⟩

def fnSc : Fn := ⟨Sc, [T0], Srt.int,
  [⟨[T0], [.var 0], some (.app boolNot [.app boolOr [.app kEq [kq (.var 0), kq nil],
      .app kEq [kq (.var 0), kq (.app cK [lit 0, nil])]]]), lit 1, none, 50, false, [], .top, .top⟩,
   ⟨[], [nil], none, lit 2, none, 50, false, [], .top, .top⟩], false⟩

def fnLf : Fn := ⟨Lf, [T0, T0], Srt.int,
  [⟨[T0, T0], [.as nil 0, .var 1], some (.app kNe [kq (.var 0), kq (.var 1)]), lit 1, none, 50, false, [], .top, .top⟩,
   ⟨[T0], [nil, .var 0], some (.app kEq [kq nil, kq (.var 0)]), lit 2, none, 50, false, [], .top, .top⟩], false⟩

def inst : Semantics := core [fnDw, fnRn, fnSc, fnLf]

theorem in_sorted : inst.sortedOK = true ∧ inst.srReady = true ∧ inst.matchReady = true := by decide_cheap

/-- `fnExclusiveL` names the four functions. -/
theorem in_L : inst.agreeObligationsL = [Dw, Rn, Sc, Lf] := by decide +kernel

/-- `fnExclusiveI` names none of them. -/
theorem in_I : inst.agreeObligationsI = [] := by decide +kernel

/-- So their equations agree. -/
theorem in_agree : ∀ fn ∈ inst.fns, ClausesAgree inst fn :=
  clausesAgree_of_I in_sorted.1 in_sorted.2.1 in_sorted.2.2 fun f hf => by
    rw [in_I] at hf; exact absurd hf List.not_mem_nil

/-! ## 5. A pair left named, whose equations disagree -/

def clW0 : Clause := ⟨[T0, Srt.int], [.as nil 0, .var 1], none, .app cK [lit 0, .var 0], none, 50, false, [], .top, .top⟩
def clW1 : Clause := ⟨[T0, Srt.int], [.var 0, .var 1], some (.app intLt [.var 1, lit 0]), .var 0, none, 50, false, [], .top, .top⟩
def fnWs : Fn := ⟨Ws, [T0, Srt.int], T0, [clW0, clW1], false⟩

def ws : Semantics := core [fnWs]

theorem ws_sorted : ws.sortedOK = true ∧ ws.srReady = true ∧ ws.matchReady = true := by decide_cheap

theorem ws_named : ws.agreeObligationsL = [Ws] ∧ ws.agreeObligationsI = [Ws] := by decide +kernel

def vNil : GroundTerm := .ctor cNil []
def vM1 : GroundTerm := .dv Srt.int (.int (-1))

theorem ws_isCtor : ws.isCtor cNil = true ∧ ws.isCtor cK = true := by decide +kernel

/-- **Ws's equations disagree**: at `(nil, -1)` the first gives `c(0, nil)`, the second `nil`. -/
theorem ws_disagree : ¬ ClausesAgree ws fnWs := by
  intro h
  have hp : (clW0, clW1) ∈ pairs fnWs.clauses := by simp [fnWs, pairs]
  have hws : ws.WellSorted clW0.vars [(0, vNil), (1, vM1)] := by
    intro i s hi
    match i, hi with
    | 0, hi => simp only [clW0, List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi
               exact ⟨vNil, rfl, by decide +kernel⟩
    | 1, hi => simp only [clW0, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hi
               subst hi; exact ⟨vM1, rfl, by decide +kernel⟩
    | _ + 2, hi => simp [clW0] at hi
  have hm0 : PatVals ws [(0, vNil), (1, vM1)] clW0.pats [vNil, vM1] :=
    .cons (.as (.ctor ws_isCtor.1 .nil) rfl) (.cons (.var rfl) .nil)
  have hm1 : PatVals ws [(0, vNil), (1, vM1)] clW1.pats [vNil, vM1] :=
    .cons (.var rfl) (.cons (.var rfl) .nil)
  have hreq : EvalTerm ws [(0, vNil), (1, vM1)] (.app intLt [.var 1, lit 0]) (some (bool true)) :=
    .hook (by decide +kernel) rfl (.cons .var (.cons .dv .nil)) (fun vs h => by cases h; rfl)
      (fun h => by cases h)
  have hdet : HDet ws [(0, vNil), (1, vM1)] clW0.rhs := by
    intro u hu
    exact plain_fun (plain_subterms (t := clW0.rhs) (by decide +kernel) hu)
  have hr0 : EvalTerm ws [(0, vNil), (1, vM1)] clW0.rhs (some (.ctor cK [.dv Srt.int (.int 0), vNil])) :=
    .ctor ws_isCtor.2 (.cons .dv (.cons .var .nil))
  have hlow : ∀ (cl : Clause), cl.prio = 50 → ∀ cl' ∈ fnWs.clauses, cl'.aside = false → cl'.prio < cl.prio →
      Fails ws [vNil, vM1] cl' := fun cl hc cl' h _ hlt => absurd hlt (by
    have : cl'.prio = 50 := by simp [fnWs, clW0, clW1] at h ⊢; rcases h with rfl | rfl <;> rfl
    rw [hc, this]; decide)
  rcases (h clW0 clW1 hp (.inl rfl)).1 [vNil, vM1] _ _ ⟨hws, hm0, (fun _ ht => by cases ht), .top⟩
      ⟨hws, hm1, (fun t ht => by cases ht; exact hreq), .top⟩ (fun _ ht => by cases ht) (fun _ _ => hdet)
      (fun _ _ ht => by cases ht) (fun hne => absurd rfl hne)
      ⟨Ws, fnWs, rfl, by simp [fnWs], by simp [fnWs], ⟨⟨hws, hm0, (fun _ ht => by cases ht), .top⟩, hlow _ rfl⟩,
        ⟨⟨hws, hm1, (fun t ht => by cases ht; exact hreq), .top⟩, hlow _ rfl⟩⟩ with ⟨-, -, hr, -⟩ | hr
  · simp [clW0, clW1] at hr
  · have := hr _ _ (.inl ⟨rfl, .inl ⟨(fun _ ht => by cases ht), .top, hr0⟩⟩)
      (.inl ⟨rfl, .inl ⟨(fun _ ht => by cases ht), .top, .var⟩⟩)
    simp [vNil] at this

/-! ## 6. Counter-example: the instance read through a map pattern -/

def clG0 : Clause := ⟨[Srt.kitem, Srt.kitem, Srt.map],
  [.app mapConcat [.app mapElem [.var 0, .var 1], .var 2]], none, .var 1, none, 50, false, [], .top, .top⟩
def clG1 : Clause := ⟨[Srt.kitem, Srt.kitem, Srt.map],
  [.app mapConcat [.app mapElem [.var 0, .var 1], .var 2]], none, .var 1, none, 50, false, [], .top, .top⟩
def fnGm : Fn := ⟨Gm, [Srt.map], Srt.kitem, [clG0, clG1], false⟩

def gm : Semantics := core [fnGm]

theorem gm_sorted : gm.sortedOK = true ∧ gm.srReady = true ∧ gm.matchReady = true := by decide_cheap

/-- `fnExclusiveI` names Gm: the map symbols are no constructors, so no instance is read. -/
theorem gm_named : gm.agreeObligationsI = [Gm] := by decide +kernel

mutual
  /-- The variant: `instOf` with any head read position by position. -/
  def instOfAny (θ : List (Nat × Term)) : Term → Term → Option (List (Nat × Term))
    | .var x, q => bindInst θ x q
    | .app f ps, .app g qs => if f == g then instOfAnyList θ ps qs else none
    | _, _ => none
  def instOfAnyList (θ : List (Nat × Term)) : List Term → List Term → Option (List (Nat × Term))
    | [], [] => some θ
    | p :: ps, q :: qs => (instOfAny θ p q).bind fun θ' => instOfAnyList θ' ps qs
    | _, _ => none
end

/-- The variant's right-hand-side case. -/
def instAgreeAny (cl cl' : Clause) : Bool :=
  match instOfAnyList [] cl.pats cl'.pats with
  | some θ => boundBy θ cl.rhs && Term.beq (substT θ cl.rhs) cl'.rhs
  | none => false

theorem instAgreeAny_Gm : instAgreeAny clG0 clG1 = true := by decide +kernel

def k1 : GroundTerm := .inj Srt.int Srt.kitem (.dv Srt.int (.int 1))
def k2 : GroundTerm := .inj Srt.int Srt.kitem (.dv Srt.int (.int 2))
def m12 : GroundTerm := .map Srt.map [(k1, k1), (k2, k2)]

theorem gm_isCtor : gm.isCtor mapConcat = false ∧ gm.isCtor mapElem = false := by decide +kernel

theorem gm_ws (a b : GroundTerm) (ha : gm.sortOf a = some Srt.kitem) (m : GroundTerm)
    (hm : gm.sortOf m = some Srt.map) (hb : gm.sortOf b = some Srt.kitem) :
    gm.WellSorted clG0.vars [(0, a), (1, b), (2, m)] := by
  intro i s hi
  match i, hi with
  | 0, hi => simp only [clG0, List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi; exact ⟨a, rfl, ha⟩
  | 1, hi => simp only [clG0, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hi
             subst hi; exact ⟨b, rfl, hb⟩
  | 2, hi => simp only [clG0, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hi
             subst hi; exact ⟨m, rfl, hm⟩
  | _ + 3, hi => simp [clG0] at hi

/-- **Gm's equations disagree**: at `{1 |-> 1, 2 |-> 2}` the first matches with K = 1, V = 1 and
the second with K' = 2, V' = 2. -/
theorem gm_disagree : ¬ ClausesAgree gm fnGm := by
  intro h
  have hp : (clG0, clG1) ∈ pairs fnGm.clauses := by simp [fnGm, pairs]
  let σ₀ : Subst := [(0, k1), (1, k1), (2, .map Srt.map [(k2, k2)])]
  let σ₁ : Subst := [(0, k2), (1, k2), (2, .map Srt.map [(k1, k1)])]
  have hm0 : PatVals gm σ₀ clG0.pats [m12] :=
    .cons (.hook (by decide) (.cons (.hook (by decide) (.cons (.var rfl) (.cons (.var rfl) .nil)) rfl)
      (.cons (.var rfl) .nil)) (by decide +kernel)) .nil
  have hm1 : PatVals gm σ₁ clG1.pats [m12] :=
    .cons (.hook (by decide) (.cons (.hook (by decide) (.cons (.var rfl) (.cons (.var rfl) .nil)) rfl)
      (.cons (.var rfl) .nil)) (by decide +kernel)) .nil
  have hdet : HDet gm σ₀ clG0.rhs := by
    intro u hu r r' h1 h2
    have hu : u = .var 1 := by simpa [clG0, subterms] using hu
    subst hu
    rw [EvalTerm.var_inv h1, EvalTerm.var_inv h2]
  have hlow : ∀ (cl : Clause), cl.prio = 50 → ∀ cl' ∈ fnGm.clauses, cl'.aside = false → cl'.prio < cl.prio →
      Fails gm [m12] cl' := fun cl hc cl' h _ hlt => absurd hlt (by
    have : cl'.prio = 50 := by simp [fnGm, clG0, clG1] at h ⊢; rcases h with rfl | rfl <;> rfl
    rw [hc, this]; decide)
  have ha0 : clG0.AppliesAt gm σ₀ [m12] :=
    ⟨gm_ws _ _ (by decide +kernel) _ (by decide +kernel) (by decide +kernel), hm0, (fun _ ht => by cases ht), .top⟩
  have ha1 : clG1.AppliesAt gm σ₁ [m12] :=
    ⟨gm_ws _ _ (by decide +kernel) _ (by decide +kernel) (by decide +kernel), hm1, (fun _ ht => by cases ht), .top⟩
  rcases (h clG0 clG1 hp (.inl rfl)).1 [m12] σ₀ σ₁ ha0 ha1 (fun _ ht => by cases ht) (fun _ _ => hdet)
      (fun _ _ ht => by cases ht) (fun hne => absurd rfl hne)
      ⟨Gm, fnGm, rfl, by simp [fnGm], by simp [fnGm], ⟨ha0, hlow _ rfl⟩, ⟨ha1, hlow _ rfl⟩⟩ with ⟨-, -, -, -, hv, -⟩ | hr
  · have := hv 1 (by simp [clG0, varOccs])
    exact absurd this (by decide +kernel)
  · have := hr _ _ (.inl ⟨rfl, .inl ⟨(fun _ ht => by cases ht), .top, .var⟩⟩)
      (.inl ⟨rfl, .inl ⟨(fun _ ht => by cases ht), .top, .var⟩⟩)
    exact absurd this (by decide +kernel)

/-! ## 7. Different priorities with an `aside` clause -/

def Pa : Sym := nRegSyms + 126
def Pb : Sym := nRegSyms + 127
def Pc : Sym := nRegSyms + 128

def clA0 : Clause := ⟨[], [lit 0], none, lit 0, none, 50, false, [], .top, .top⟩
def clA1 : Clause := ⟨[Srt.int], [.var 0], none, .var 0, none, 60, true, [], .top, .top⟩
def fnPa : Fn := ⟨Pa, [Srt.int], Srt.int, [clA0, clA1], false⟩

def clB0 : Clause := ⟨[], [lit 0], none, lit 1, none, 60, false, [], .top, .top⟩
def clB1 : Clause := ⟨[Srt.int], [.var 0], none, .var 0, none, 50, true, [], .top, .top⟩
def fnPb : Fn := ⟨Pb, [Srt.int], Srt.int, [clB0, clB1], false⟩

def clC0 : Clause := { clB0 with aside := true }
def fnPc : Fn := ⟨Pc, [Srt.int], Srt.int, [clC0, clB1], false⟩

def pa : Semantics := core [fnPa, fnPb, fnPc]

theorem pa_sorted : pa.sortedOK = true ∧ pa.srReady = true ∧ pa.matchReady = true := by decide_cheap

/-- The premise `ClausesAgree` reads of Pa's pair is false: nothing is asked of it. -/
theorem pa_premise : ¬ (clA0.prio = clA1.prio ∨ (clA0.aside = true ∧ clA0.prio < clA1.prio) ∨
    (clA1.aside = true ∧ clA1.prio < clA0.prio)) := by decide +kernel

/-- Pb's pair competes (the `aside` clause is the smaller), and so does Pc's. -/
theorem pb_premise : (clB0.prio = clB1.prio ∨ (clB0.aside = true ∧ clB0.prio < clB1.prio) ∨
    (clB1.aside = true ∧ clB1.prio < clB0.prio)) ∧
    (clC0.prio = clB1.prio ∨ (clC0.aside = true ∧ clC0.prio < clB1.prio) ∨
    (clB1.aside = true ∧ clB1.prio < clC0.prio)) := by decide +kernel

theorem pa_notCompeting : notCompeting clA0 clA1 = true ∧ notCompeting clA1 clA0 = true ∧
    notCompeting clB0 clB1 = false ∧ notCompeting clB1 clB0 = false ∧ notCompeting clC0 clB1 = false := by
  decide +kernel

/-- `fnExclusiveL` names the three; `fnExclusiveI` names Pb and Pc only. -/
theorem pa_named : pa.agreeObligationsL = [Pa, Pb, Pc] ∧ pa.agreeObligationsI = [Pb, Pc] := by decide +kernel

/-- The same for the pair as `fnExclusiveIO` reads it (a definition with overloading symbols). -/
theorem pa_pairO : pa.pairAgreeO (pa.fns.map Fn.sig) clA0 clA1 = true ∧
    pa.pairAgreeO (pa.fns.map Fn.sig) clB0 clB1 = false ∧
    pa.pairAgreeO (pa.fns.map Fn.sig) clC0 clB1 = false := by decide +kernel

theorem pb_named : Pb ∈ pa.agreeObligationsI ∧ Pc ∈ pa.agreeObligationsI := by rw [pa_named.2]; decide

/-- Pa's equations agree, by the decider's lemma. -/
theorem pa_agree : ClausesAgree pa fnPa :=
  (fnExclusiveI_sound (Exec.matchCtx_of pa_sorted.2.2) (fun _ _ => ovlFreeList_of_nil rfl _)
    (fun cl h => by
      have := Semantics.sortedOK_sorted pa_sorted.1
      simp only [Bool.and_eq_true, List.all_eq_true] at this
      exact this.1.2 fnPa (by simp [pa, core]) cl h)
    (by decide +kernel)).agree (Semantics.fnsNoExs_of_sortedOK pa_sorted.1 fnPa (by simp [pa, core]))

end KCore.AgreeInstTest

#print axioms KCore.AgreeInstTest.pa_agree

#print axioms KCore.AgreeInstTest.in_agree
#print axioms KCore.AgreeInstTest.ws_disagree
#print axioms KCore.AgreeInstTest.gm_disagree
