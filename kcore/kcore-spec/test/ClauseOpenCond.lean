/-
  Clauses whose closed `requires` holds a variable the arguments do not bind, at the level of
  `Eval`, `needsWitness` and `Clause.Witnessed`, with no use of `coreOK` but in the last section
  (e2-cool-eq's owed `CondDecided` from its witness, and the pinned `sound_at` there with no
  hypothesis left: `Cool.hc_witDet`, `Cool.sound_at_witDet`). Run from the package
  root: `lake env lean -j1 test/ClauseOpenCond.lean`. Kernel-checked (`decide +kernel`).

  Each clause is written by hand and shown to be the reader's for its kompiled text (`text`):
  - `Cool.clCool`, e2-cool-eq's `f(X) => X [cool]` (`f2-examples/cooleq.kompile.kore`), which
    kompile writes `f(X) => X requires true andBool isKResult(HOLE:K)`: HOLE is of K, which is not
    confined, so the clause needs a witness. HOLE := `kseq(inj{Int,KItem}(0), dotk)` witnesses
    it: `isKResult` of it is `true` and nothing else (`Int` is below `KResult`), so the
    `requires` has the result `true` and no other (`Cool.witnessed`); and `f(3)` is `3`
    (`Cool.eval_f3`).
  - `Title.clH`, `f() => 0 requires 1 ==Int 2 *Int H` (`f2-examples/openh.kompile.kore`): it
    needs a witness and has none: no Int n has `1 = 2 * n` (`Title.not_witnessed`).
  - `Genless.clG`, `f(_) => 1 requires isC(H:S)` beside `f(_) => 0 [owise]`
    (`f2-examples/clgenless.kompile.kore`, the variant with an argument of CX-F 5's text, S ::= "a"
    | c(Empty), Empty without a value): it needs a witness and has none: `isC` is `true` only at
    `c(e)`, and no value e has sort Empty (`Genless.not_witnessed`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace ClauseOpenCond

/-! ## e2-cool-eq -/

namespace Cool

definition_of defn from "f2-examples/cooleq.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- The symbols and sorts the clause names. -/
example : c.symName 385 = "Lblf" ∧ c.symName 382 = "LblisKResult" ∧ c.symName 4 = "Lbl'Unds'andBool'Unds'" ∧
    c.sortName 32 = "KResult" := by
  decide +kernel

/-- `f(X) => X requires true andBool isKResult(HOLE)`, X:Int, HOLE:K -/
def clCool : Clause :=
  { vars := [Srt.int, Srt.k], pats := [.var 0],
    req := some (.app 4 [.dv Srt.bool (.bool true), .app 382 [.var 1]]), rhs := .var 0, ens := none }
def fCool : Fn := { label := 385, args := [Srt.int], result := Srt.int, clauses := [clCool] }

/-- `isKResult(kseq(inj{KResult,KItem}(V), dotk)) = true`, V:KResult -/
def kr1 : Clause :=
  { vars := [32], pats := [.app kseq [.inj 32 Srt.kitem (.var 0), .app dotk []]], req := none,
    rhs := .dv Srt.bool (.bool true), ens := none }
/-- otherwise `false` -/
def kr2 : Clause :=
  { vars := [Srt.k], pats := [.var 0], req := none, rhs := .dv Srt.bool (.bool false), ens := none, prio := 200 }
def fKR : Fn := ⟨382, [Srt.k], Srt.bool, [kr1, kr2], true⟩

/-- The reader's function `f` is `fCool`; `isKResult` is the generated predicate `fKR`. -/
theorem text : c.fns = [fCool] := by rfl
theorem lookupF : c.lookupFn 385 = some fCool := by rfl
theorem lookupKR : c.lookupFn 382 = some fKR := by rfl

/-- The clause needs a witness: its condition holds HOLE only, of K, which is not confined. -/
theorem needs : clCool.needsWitness c = true ∧ c.confined Srt.k = false ∧ clCool.condVars = [1] := by
  decide +kernel

/-- `kseq(inj{Int,KItem}(0), dotk)` -/
def hole : GroundTerm := .ctor kseq [.inj Srt.int Srt.kitem (.dv Srt.int (.int 0)), .ctor dotk []]

theorem hole_sort : c.sortOf hole = some Srt.k := by decide +kernel

/-- V := `inj{Int,KResult}(0)`, the match of `kr1` at `hole`. -/
def σV : Subst := [(0, .inj Srt.int 32 (.dv Srt.int (.int 0)))]

theorem σV_sorted : c.WellSorted kr1.vars σV := fun i s hs => by
  cases i with
  | zero => cases (show some (32 : Srt) = some s from hs); exact ⟨_, rfl, by decide +kernel⟩
  | succ i => cases (show (none : Option Srt) = some s from hs)

theorem kr1_match : PatVals c σV kr1.pats [hole] :=
  .cons (.ctor (by decide +kernel)
    (.cons (PatVal.inj (w := .inj Srt.int 32 (.dv Srt.int (.int 0))) (.var rfl))
      (.cons (.ctor (by decide +kernel) .nil) .nil))) .nil

/-- `kr1` applies at `hole`, so it does not fail there. -/
theorem kr1_not_fails : ¬ Fails c [hole] kr1 := by
  rintro ⟨h⟩
  cases h σV (fun i _ s hs => σV_sorted i s hs) kr1_match with
  | intro ht _ _ => cases ht
  | pre h => exact absurd (Holds.top_eq h) (by simp)

/-- **`isKResult(hole)` is `true`**, by `kr1`. -/
theorem kr_hole : Eval c 382 [hole] (some (bool true)) :=
  .clause lookupKR (List.mem_cons_self ..) σV_sorted kr1_match (fun _ ht => by cases ht) .top
    (fun cl' hcl' _ hlt => by
      rcases List.mem_cons.mp hcl' with rfl | hcl'
      · exact absurd hlt (by decide)
      · rw [List.mem_singleton.mp hcl'] at hlt; exact absurd hlt (by decide))
    rfl .dv (fun _ ht => by cases ht) .top

/-- **and nothing else**: `kr2` and the rest are blocked by `kr1`, which applies. -/
theorem kr_hole_only {r : Option GroundTerm} (h : Eval c 382 [hole] r) : r = some (bool true) := by
  cases h with
  | clause hfn hmem _ _ _ _ hprio _ hrhs _ _ =>
    rw [lookupKR] at hfn; cases hfn
    rcases List.mem_cons.mp hmem with rfl | hmem
    · cases hrhs; rfl
    · obtain rfl := List.mem_singleton.mp hmem
      exact absurd (hprio kr1 (List.mem_cons_self ..) rfl (by decide)) kr1_not_fails
  | rest hfn hnone =>
    rw [lookupKR] at hfn; cases hfn
    exact absurd (hnone kr1 (List.mem_cons_self ..)) kr1_not_fails
  | ensFails hfn hmem _ _ _ _ _ _ ht _ _ =>
    rw [lookupKR] at hfn; cases hfn
    rcases List.mem_cons.mp hmem with rfl | hmem
    · cases ht
    · rw [List.mem_singleton.mp hmem] at ht; cases ht
  | clauseEx hfn hmem _ _ _ _ _ hne =>
    rw [lookupKR] at hfn; cases hfn
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact absurd rfl hne
    · rw [List.mem_singleton.mp hmem] at hne; exact absurd rfl hne
  | exNone hfn hmem hne =>
    rw [lookupKR] at hfn; cases hfn
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact absurd rfl hne
    · rw [List.mem_singleton.mp hmem] at hne; exact absurd rfl hne

/-- `isKResult(HOLE)` under a σ giving HOLE `hole`: `true`, and nothing else. -/
theorem call_kr {σ : Subst} (h1 : σ.lookup 1 = some hole) :
    EvalTerm c σ (.app 382 [.var 1]) (some (bool true)) :=
  .call (vs := [hole]) (by decide +kernel) (by decide +kernel) (.cons .var .nil) (by rw [h1]; rfl) kr_hole
    (by decide +kernel)

theorem call_kr_only {σ : Subst} (h1 : σ.lookup 1 = some hole) {r : Option GroundTerm}
    (h : EvalTerm c σ (.app 382 [.var 1]) r) : r = some (bool true) := by
  cases h with
  | ctor h _ => exact absurd h (by decide +kernel)
  | hook _ hhk _ _ _ => exact absurd hhk (by decide +kernel)
  | param _ _ hp _ _ => exact absurd hp (by decide +kernel)
  | call _ _ hts hvs hf _ =>
    cases hts with
    | cons ha hs =>
      cases ha; cases hs
      rw [h1] at hvs
      cases (show some [hole] = some _ from hvs)
      exact kr_hole_only hf
  | callUndef _ _ hts hvs _ =>
    cases hts with
    | cons ha hs => cases ha; cases hs; rw [h1] at hvs; cases hvs
  | ovl _ ho _ => exact absurd ho (by decide +kernel)
  | ovlFn _ ho => exact absurd ho (by decide +kernel)

/-- The `requires` under a σ giving HOLE `hole`: `true andBool true`, so `true` ... -/
theorem req_true {σ : Subst} (h1 : σ.lookup 1 = some hole) :
    EvalTerm c σ (.app 4 [.dv Srt.bool (.bool true), .app 382 [.var 1]]) (some (bool true)) :=
  .hook (by decide +kernel) (by decide +kernel) (.cons .dv (.cons (call_kr h1) .nil))
    (fun vs hvs => by cases hvs; rfl) (fun h => by cases h)

/-- ... and nothing else. -/
theorem req_only {σ : Subst} (h1 : σ.lookup 1 = some hole) {r : Option GroundTerm}
    (h : EvalTerm c σ (.app 4 [.dv Srt.bool (.bool true), .app 382 [.var 1]]) r) : r = some (bool true) := by
  cases h with
  | ctor h _ => exact absurd h (by decide +kernel)
  | hook _ _ hts hh _ =>
    cases hts with
    | cons ha hs =>
      cases ha
      cases hs with
      | cons hb hs' =>
        cases hs'
        cases call_kr_only h1 hb
        have h4 : c.hookRes 4 [.dv Srt.bool (.bool true), .dv Srt.bool (.bool true)] =
            some (some (.dv Srt.bool (.bool true))) := by rfl
        exact (Option.some.inj ((hh _ rfl).symm.trans h4)).symm ▸ rfl
  | param _ hhk _ _ _ => exact absurd hhk (by decide +kernel)
  | call _ hh _ _ _ _ => exact absurd hh (by decide +kernel)
  | callUndef _ hh _ _ _ => exact absurd hh (by decide +kernel)
  | ovl _ ho _ => exact absurd ho (by decide +kernel)
  | ovlFn _ ho => exact absurd ho (by decide +kernel)

/-- **`clCool` is `Witnessed`** at HOLE := `kseq(inj{Int,KItem}(0), dotk)`. -/
theorem witnessed : clCool.Witnessed c := by
  refine Clause.witnessed_of_top rfl (σ := [(1, hole)]) (fun j hj s hs => ?_) (fun t ht => ?_)
  · rw [needs.2.2] at hj
    cases List.mem_singleton.mp hj
    cases (show some Srt.k = some s from hs)
    exact ⟨hole, rfl, hole_sort⟩
  · cases ht
    exact ⟨req_true rfl, fun r hr => req_only rfl hr⟩

/-- **`f(3)` is `3`**: X := 3, HOLE := `hole`. -/
theorem eval_f3 : Eval c 385 [.dv Srt.int (.int 3)] (some (.dv Srt.int (.int 3))) :=
  .clause (σ := [(0, .dv Srt.int (.int 3)), (1, hole)]) lookupF (List.mem_singleton_self _)
    (fun i s hs => by
      match i, hs with
      | 0, hs => cases (show some Srt.int = some s from hs); exact ⟨_, rfl, sortOf_int 3⟩
      | 1, hs => cases (show some Srt.k = some s from hs); exact ⟨_, rfl, hole_sort⟩
      | _ + 2, hs => cases (show (none : Option Srt) = some s from hs))
    (.cons (.var rfl) .nil) (fun _ ht => by cases ht; exact req_true rfl) .top
    (fun cl' hcl' _ hlt => by rw [List.mem_singleton.mp hcl'] at hlt; exact absurd hlt (by decide))
    rfl .var (fun _ ht => by cases ht) .top

end Cool

/-! ## The title clause: `f() => 0 requires 1 ==Int 2 *Int H` -/

namespace Title

definition_of defn from "f2-examples/openh.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

example : c.symName 385 = "Lblf" ∧ c.symName intEq = "Lbl'UndsEqlsEqls'Int'Unds'" ∧
    c.symName intMul = "Lbl'UndsStar'Int'Unds'" := by
  decide +kernel

/-- `f() => 0 requires 1 ==Int 2 *Int H`, H:Int -/
def clH : Clause :=
  { vars := [Srt.int], pats := [],
    req := some (.app intEq [.dv Srt.int (.int 1), .app intMul [.dv Srt.int (.int 2), .var 0]]),
    rhs := .dv Srt.int (.int 0), ens := none }
def fH : Fn := { label := 385, args := [], result := Srt.int, clauses := [clH] }

theorem text : c.fns = [fH] := by rfl

/-- The clause needs a witness: H, of Int, which is not confined, is its condition's only variable. -/
theorem needs : clH.needsWitness c = true ∧ c.confined Srt.int = false ∧ clH.condVars = [0] := by
  decide +kernel

/-- A value of Int is an Int literal. -/
theorem int_value {v : GroundTerm} (h : c.sortOf v = some Srt.int) : ∃ n, v = .dv Srt.int (.int n) := by
  have hs : c.shapesOK = true ∧ shapeSorts.contains Srt.int = true ∧ c.collOf Srt.int = none ∧
      c.lib.carrier Srt.int = Srt.int ∧ c.lib.tokenSorts.contains Srt.int = false ∧
      c.lib.byteSorts.contains Srt.int = false := by
    decide +kernel
  rcases shape_of_sortOf hs.1 hs.2.1 h with ⟨lit, rfl, hok⟩ | ⟨_, k, -, hk, -⟩ | ⟨_, k, -, hk, -⟩ | ⟨_, k, -, hk, -⟩
  · cases lit with
    | int n => exact ⟨n, rfl⟩
    | bool _ => simp only [dvOK, hs.2.2.2.1] at hok; exact absurd hok (by decide)
    | float _ _ _ => simp only [dvOK, hs.2.2.2.1, Bool.and_eq_true] at hok; exact absurd hok.1 (by decide)
    | tok _ =>
      simp only [dvOK, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2, Bool.or_false,
        Bool.or_eq_true, Bool.and_eq_true] at hok
      rcases hok with (hok | hok) | ⟨hok, -⟩
      · exact absurd hok (by decide)
      · exact absurd hok (by decide)
      · exact absurd hok (by decide)
  all_goals (rw [hs.2.2.1] at hk; cases hk)

/-- **`clH` is not `Witnessed`**: at H := n the `requires` is `1 ==Int 2 *Int n`, which is `true`
only where 1 = 2 * n, and no integer n is one. -/
theorem not_witnessed : ¬ clH.Witnessed c := by
  intro hW
  obtain ⟨σ, hσ, hreq, -⟩ := hW.conds
  obtain ⟨v, hv, hvs⟩ := hσ 0 (by rw [needs.2.2]; exact List.mem_singleton_self _) Srt.int rfl
  obtain ⟨n, rfl⟩ := int_value hvs
  have he := (hreq _ rfl).1
  generalize hr0 : some (bool true) = r at he
  cases he with
  | ctor h _ => exact absurd h (by decide +kernel)
  | hook _ _ hts hh _ =>
    cases hts with
    | cons ha hs =>
      cases ha
      cases hs with
      | cons hb hs' =>
        cases hs'
        cases hb with
        | ctor h _ => exact absurd h (by decide +kernel)
        | hook _ _ hts' hh' _ =>
          cases hts' with
          | cons ha' hs1 =>
            cases ha'
            cases hs1 with
            | cons hb' hs2 =>
              cases hb'
              cases hs2
              rw [hv] at hh'
              have hm : c.hookRes intMul [.dv Srt.int (.int 2), .dv Srt.int (.int n)] =
                  some (some (.dv Srt.int (.int (2 * n)))) := by rfl
              have hr := Option.some.inj ((hh' _ rfl).symm.trans hm)
              subst hr
              have he' : c.hookRes intEq [.dv Srt.int (.int 1), .dv Srt.int (.int (2 * n))] =
                  some (some (.dv Srt.bool (.bool (1 == 2 * n)))) := by rfl
              have hb := Option.some.inj (hr0.trans (Option.some.inj ((hh _ rfl).symm.trans he')))
              have h12 : (1 == 2 * n) = true := by
                cases hb' : (1 == 2 * n)
                · rw [hb'] at hb; cases hb
                · rfl
              have := beq_iff_eq.mp h12
              omega
        | param _ hk1 _ _ _ => exact absurd hk1 (by decide +kernel)
        | call _ hk2 _ _ _ _ => exact absurd hk2 (by decide +kernel)
        | callUndef _ hk3 _ _ _ => exact absurd hk3 (by decide +kernel)
        | ovl _ hk4 _ => exact absurd hk4 (by decide +kernel)
        | ovlFn _ hk4 => exact absurd hk4 (by decide +kernel)
  | param _ hhk _ _ _ => exact absurd hhk (by decide +kernel)
  | call _ hh _ _ _ _ => exact absurd hh (by decide +kernel)
  | callUndef _ hh _ _ _ => exact absurd hh (by decide +kernel)
  | ovl _ ho _ => exact absurd ho (by decide +kernel)
  | ovlFn _ ho => exact absurd ho (by decide +kernel)

end Title

/-! ## The genless clause: `f(_) => 1 requires isC(H:S)` -/

namespace Genless

definition_of defn from "f2-examples/clgenless.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

example : c.symName 389 = "Lblf" ∧ c.symName 390 = "LblisC" ∧ c.symName 387 = "Lblc" ∧
    c.sortName 32 = "S" ∧ c.sortName 33 = "Empty" := by
  decide +kernel

/-- `f(X) => 1 requires isC(H)`, X:Int, H:S -/
def clG : Clause :=
  { vars := [Srt.int, 32], pats := [.var 0], req := some (.app 390 [.var 1]), rhs := .dv Srt.int (.int 1),
    ens := none }
/-- `f(_) => 0 [owise]` -/
def clO : Clause := { vars := [Srt.int], pats := [.var 0], req := none, rhs := .dv Srt.int (.int 0), ens := none, prio := 200 }
def fG : Fn := { label := 389, args := [Srt.int], result := Srt.int, clauses := [clG, clO] }
/-- `isC(c(_)) => true` -/
def ic1 : Clause := { vars := [33], pats := [.app 387 [.var 0]], req := none, rhs := .dv Srt.bool (.bool true), ens := none }
/-- `isC(_) => false [owise]` -/
def ic2 : Clause := { vars := [32], pats := [.var 0], req := none, rhs := .dv Srt.bool (.bool false), ens := none, prio := 200 }
def fIsC : Fn := { label := 390, args := [32], result := Srt.bool, clauses := [ic1, ic2], total := true }

theorem text : c.fns = [fG, fIsC] := by rfl
theorem lookupIsC : c.lookupFn 390 = some fIsC := by rfl

/-- The clause needs a witness: S is not confined (its generator `c` takes a sort without a value). -/
theorem needs : clG.needsWitness c = true ∧ c.confined 32 = false ∧ clG.condVars = [1] := by
  decide +kernel

/-- The facts on Empty that `no_E` reads. -/
theorem emptyFacts : c.ctorSigs.all (·.result != 33) = true ∧ c.ovls = [] ∧
    c.subsorts.all (fun p => p.2 != 33) = true ∧ c.collOf 33 = none ∧ c.lib.carriers.all (·.1 != 33) = true := by
  decide +kernel

/-- No parameter is raw (`sortOf`'s open-generator arm reads none, `no_E`). -/
theorem noRaw_intA1 : (c.params.all fun k => !k.raw) = true := by
  decide +kernel

/-- **No value has sort Empty**: no constructor and no subsort pair ends there, no literal is of
it, and it is no collection sort. -/
theorem no_E (v : GroundTerm) : c.sortOf v ≠ some 33 := by
  intro h
  cases v with
  | ctor f ts =>
    rw [Semantics.sortOf] at h
    cases hk : lookupSig c.ctorSigs f with
    | none =>
      have : c.lookupOvl f = none := by simp [Semantics.lookupOvl, emptyFacts.2.1]
      have ho : c.lookupOpen f = none := c.lookupOpen_of_noRaw
        (fun k hk => by simpa using List.all_eq_true.mp noRaw_intA1 k hk) f
      rw [hk, this, ho] at h; cases h
    | some k =>
      rw [hk] at h
      simp only at h
      split at h
      · have hm := List.mem_of_find?_eq_some (by rw [← lookupSig_eq]; exact hk)
        have := List.all_eq_true.mp emptyFacts.1 k hm
        rw [Option.some.inj h] at this
        simp at this
      · cases h
  | inj a b t =>
    rw [Semantics.sortOf] at h
    split at h
    · rename_i h'
      cases h
      simp only [Bool.and_eq_true, List.contains_iff_mem] at h'
      have := List.all_eq_true.mp emptyFacts.2.2.1 _ h'.1.1
      simp at this
    · cases h
  | dv s' lit =>
    obtain ⟨hd, rfl⟩ := sortOf_dv.mp h
    have hcs := Lib.carrier_of_not _ emptyFacts.2.2.2.2
    cases lit with
    | int _ => simp only [dvOK, hcs, beq_iff_eq] at hd; exact absurd hd (by decide)
    | bool _ => simp only [dvOK, hcs, beq_iff_eq] at hd; exact absurd hd (by decide)
    | float _ _ _ => simp only [dvOK, hcs, Bool.and_eq_true, beq_iff_eq] at hd; exact absurd hd.1 (by decide)
    | tok t =>
      simp only [dvOK, hcs, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hd
      rcases hd with ((hd | hd) | hd) | ⟨hd | hd, -⟩
      · exact absurd hd (by decide)
      · exact absurd hd (by decide)
      · exact absurd hd (by decide +kernel)
      · exact absurd hd (by decide)
      · exact absurd hd (by decide +kernel)
  | map s' es =>
    obtain ⟨k, -, hco, -, -, -, -, rfl⟩ := sortOf_mapS_fwd h
    rw [emptyFacts.2.2.2.1] at hco; cases hco
  | set s' es =>
    obtain ⟨k, hco, -, -, -, rfl⟩ := sortOf_setS.mp h
    rw [emptyFacts.2.2.2.1] at hco; cases hco
  | list s' es =>
    obtain ⟨k, hco, -, -, rfl⟩ := sortOf_listS.mp h
    rw [emptyFacts.2.2.2.1] at hco; cases hco

/-- **`isC` is `true` at no argument**: `ic1` decides only under a value of Empty, and `ic2` gives
`false`; the rest (`fnRest`) is undefined here: the reader's semantics interprets no symbol. -/
theorem isC_not_true (v : GroundTerm) : ¬ Eval c 390 [v] (some (bool true)) := by
  intro h
  cases h with
  | clause hfn hmem hσ _ _ _ _ _ hrhs _ _ =>
    rw [lookupIsC] at hfn; cases hfn
    rcases List.mem_cons.mp hmem with rfl | hmem
    · obtain ⟨w, -, hw⟩ := hσ 0 33 rfl
      exact no_E w hw
    · rw [List.mem_singleton.mp hmem] at hrhs; cases hrhs
  | clauseEx hfn hmem _ _ _ _ _ hne =>
    rw [lookupIsC] at hfn; cases hfn
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact absurd rfl hne
    · rw [List.mem_singleton.mp hmem] at hne; exact absurd rfl hne

/-- **`clG` is not `Witnessed`**: H must be a value of S, and `isC` is `true` at none. -/
theorem not_witnessed : ¬ clG.Witnessed c := by
  intro hW
  obtain ⟨σ, hσ, hreq, -⟩ := hW.conds
  obtain ⟨v, hv, hvs⟩ := hσ 1 (by rw [needs.2.2]; exact List.mem_singleton_self _) 32 rfl
  have he := (hreq _ rfl).1
  generalize hr0 : some (bool true) = r at he
  cases he with
  | ctor h _ => exact absurd h (by decide +kernel)
  | hook _ hhk _ _ _ => exact absurd hhk (by decide +kernel)
  | param _ _ hp _ _ => exact absurd hp (by decide +kernel)
  | call _ _ hts hvs' hf _ =>
    cases hts with
    | cons ha hs =>
      cases ha; cases hs
      rw [hv] at hvs'
      cases (show some [v] = some _ from hvs')
      subst hr0
      exact isC_not_true v hf
  | callUndef _ _ hts hvs' _ =>
    cases hts with
    | cons ha hs => cases ha; cases hs; rw [hv] at hvs'; cases hvs'
  | ovl _ ho _ => exact absurd ho (by decide +kernel)
  | ovlFn _ ho => exact absurd ho (by decide +kernel)

end Genless

/-! ## e2-cool-eq's owed fact, discharged by the witness -/

namespace Cool

/-- **The clauses' hypothesis of the pinned statements at e2-cool-eq**: its one clause needing a
witness is `Witnessed` (`witnessed`), so its `CondDecided`, which the account lists as owed, holds. -/
theorem hc_witDet : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c := by
  intro fn hfn cl hcl _
  rw [text] at hfn
  cases List.mem_singleton.mp hfn
  cases List.mem_singleton.mp hcl
  exact Or.inl witnessed

/-- The text is `coreOK`, and no rule needs a witness. -/
theorem core_witDet : c.coreOK = true ∧ c.rules.all (fun r => !r.needsWitness c) = true := by
  decide_cheap

/-- **`sound_at` at e2-cool-eq with no hypothesis left**: the clause side from `hc_witDet`, the rule
side vacuous. -/
theorem sound_at_witDet (x y : Config c) (r : Rule) (σ : Subst) (hs : StepBy c r σ x y) :
    (Faithful.Γc c ⊧ (den c x.val ⇒ KoreAML.sNext (Faithful.famEx c r σ))) ∧
      (Faithful.Γc c ⊧ (den c y.val ⇒ Faithful.famEx c r σ)) :=
  sound_at c core_witDet.1 x y r σ hs
    (fun r' hr' _ hw _ => absurd hw (by
      have := List.all_eq_true.mp core_witDet.2 r' hr'
      simpa using this))
    hc_witDet

end Cool

/-- info: 'ClauseOpenCond.Cool.witnessed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Cool.witnessed
/-- info: 'ClauseOpenCond.Cool.sound_at_witDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Cool.sound_at_witDet
/-- info: 'ClauseOpenCond.Title.not_witnessed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Title.not_witnessed
/-- info: 'ClauseOpenCond.Genless.not_witnessed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Genless.not_witnessed

end ClauseOpenCond
