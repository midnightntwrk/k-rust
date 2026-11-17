/-
  KCore, checked layer: a library equation in the function form with the `owise` premise is
  entailed at values (`EntailsAtValues`), for every semantics meeting `coreOK` and every
  interpretation.

  kompile writes an `[owise]` equation of a function `f` as the function form (`LibEv.FnEqn`) whose
  premise has one more conjunct, first: the negation of the premises of `f`'s other equations,

    \and{R}(\not{R}(\or{R}(O1, \or{R}(O2, … \bottom{R}()))), \and{R}(prem, ins))

  where each `Oi` is the premise `\and{R}(prem_i, ins_i)` of another equation, over the same
  argument variables `X0 … Xn`, under `\exists{R}` binders of that equation's own variables.

  - `LibEv.FnOther`: another equation as the premise names it: its variables in the order of the
    binders, its patterns and its `requires`, over the equation's variables then its own.
  - `LibEv.FnOwise`: an equation with the other equations of its function.
  - `FnOwise.Holds`: `FnEqn.Holds` where, in addition, no other equation applies: at no extension
    of the substitution by values of an other equation's variables does its `requires` have the
    value `true` and its patterns match.
  - `FnEqn.entailed_owise`, `FnEqn.entailed_owise_reg`: an `[owise]` equation that holds is entailed at
    values, whatever axiom declaration of a text holds its pattern.

  The translation of `\exists{R}(x:s, φ)` is `sExists` at the table's variable of `x`: its body is
  read at the valuation updated there. `FnEqn.entailed` reads a premise from the translation to the
  values; the `owise` conjunct is a negation, so here the converse is needed, from values to the
  translated premise of an other equation, at the valuation updated at its binders:
  - `fo_hag_upd`: where `R`, the equation's variables and the other equation's have distinct places
    in the axiom's table (`apartIn`), the valuation updated at the binders, each to the element of
    its value, still gives every variable its value's element (the premise `LibEv.den_val` reads)
    and `R` its sort;
  - `fo_exs_intro`, `fo_req_intro`, `fo_ins_intro`: then the binders, the `requires` with the value
    `true`, and the matching patterns hold.

  - `fnReplaceOw` (domains.md 1915, K 7.1.337): `replace(Source, _, _, Count) => Source requires
    Count >=Int 0 [owise]`, beside the equation 1911 for `Count >Int 0 andBool
    findString(Source, ToReplace, 0) >=Int 0`; `fnReplaceOw_ev`. Without the premise the equation
    `fnReplaceEq` does not hold: `replace("a", "a", "b", 1)` is "b".
-/
import KcoreSpec.LibEvFnLib
import KcoreSpec.ExistsHoist

set_option autoImplicit false

namespace KCore

namespace LibEv

open ML Faithful

/-- Another equation of a function as an `owise` premise names it: its variables in the order the
`\exists` binders bind them, its patterns of the arguments and its `requires`, terms over the
`[owise]` equation's variables (`FnEqn.av`) followed by these. -/
structure FnOther where
  vars : Vars
  pats : List FnPat
  req : Option Term

/-- An `[owise]` equation: the equation, and the other equations of its function. -/
structure FnOwise where
  eqn : FnEqn
  others : List FnOther

namespace FnOwise

/-- The variables of an other equation's premise: the `[owise]` equation's, then its own. -/
def ovs (W : FnOwise) (O : FnOther) : Vars := W.eqn.av ++ O.vars

/-- The `\exists{R}` binders of the variables `vs` around `p`, the first outermost. -/
def exs (k : Srt → Kore.KSort) : Vars → Kore.Pattern → Kore.Pattern
  | [], p => p
  | v :: vs, p => .exist KoreAML.R (KoreAML.evar v.1 (k v.2)) (exs k vs p)

/-- The first conjunct of a premise, over the variables `vs`. -/
def reqO (c : Semantics) (vs : Vars) : Option Term → Kore.Pattern
  | none => .top KoreAML.R
  | some q => .equals (srtOf c Srt.bool) KoreAML.R (kore c vs q) (.dv (srtOf c Srt.bool) "true")

/-- An other equation's premise under its binders. -/
def other (c : Semantics) (W : FnOwise) (O : FnOther) : Kore.Pattern :=
  exs (srtOf c) O.vars
    (.and KoreAML.R [reqO c (W.ovs O) O.req, FnEqn.ins c (W.ovs O) W.eqn.vars.length O.pats])

/-- `\or{R}(p1, \or{R}(p2, … \bottom{R}()))`. -/
def alts : List Kore.Pattern → Kore.Pattern
  | [] => .bottom KoreAML.R
  | p :: ps => .or KoreAML.R [p, alts ps]

/-- The `owise` conjunct: no other equation's premise. -/
def owiseP (c : Semantics) (W : FnOwise) : Kore.Pattern :=
  .not KoreAML.R (alts (W.others.map (W.other c)))

/-- The pattern of the `[owise]` equation's axiom, as kompile writes it over the sort variable `R`. -/
def pattern (c : Semantics) (W : FnOwise) : Kore.Pattern :=
  .implies KoreAML.R
    (.and KoreAML.R [W.owiseP c, .and KoreAML.R [W.eqn.reqP c, FnEqn.ins c W.eqn.av W.eqn.vars.length W.eqn.pats]])
    (.equals (srtOf c W.eqn.s) KoreAML.R (kore c W.eqn.av W.eqn.lhs)
      (.and (srtOf c W.eqn.s) [kore c W.eqn.av W.eqn.rhs, .top (srtOf c W.eqn.s)]))

/-- An other equation is over registry sorts, its patterns are terms of the argument sorts and its
`requires` a term of the sort Bool. -/
def otherTyped (c : Semantics) (W : FnOwise) (O : FnOther) : Bool :=
  O.vars.all (fun p => decide (p.2 < nRegSorts)) &&
  FnEqn.patsTyped c (W.ovs O) W.eqn.vars.length O.pats &&
  match O.req with
  | none => true
  | some q => srt? c (W.ovs O) q == some Srt.bool

/-- The keys of the variables `vs`. -/
def keys (k : Srt → Kore.KSort) (vs : Vars) : List KoreAML.VarKey := vs.map fun p => .evar p.1 (k p.2)

/-- In the table `t`, the sort variable `R`, the equation's variables and an other equation's
variables have distinct places. -/
def apartIn (t : KoreAML.VarTable) (k : Srt → Kore.KSort) (W : FnOwise) (O : FnOther) : Bool :=
  decide (((KoreAML.sortVarKey KoreAML.Rv :: keys k (W.ovs O)).map t.idxOf).Nodup)

/-- The `[owise]` equation holds of the values: `FnEqn.Holds` at the substitutions at which, in
addition, no other equation applies: at no substitution that agrees on the equation's variables
and gives an other equation's variables values of their sorts does its `requires` have the value
`true` and its patterns match the arguments. -/
def Holds (c : Semantics) (W : FnOwise) : Prop :=
  ∀ σ : Subst, (∀ i p, W.eqn.av[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2) →
    (∀ q, W.eqn.req = some q → val c σ q = some (bool true)) →
    FnEqn.Matches c σ W.eqn.vars.length W.eqn.pats →
    (∀ O ∈ W.others, ∀ σ' : Subst, (∀ i, i < W.eqn.av.length → σ'.lookup i = σ.lookup i) →
      (∀ j p, O.vars[j]? = some p → ∃ v, σ'.lookup (W.eqn.av.length + j) = some v ∧ c.sortOf v = some p.2) →
      (∀ q, O.req = some q → val c σ' q = some (bool true)) →
      ¬ FnEqn.Matches c σ' W.eqn.vars.length O.pats) →
    val c σ W.eqn.lhs = val c σ W.eqn.rhs

/-! ### Over the registry's names -/

/-- `reqO` with the registry's names. -/
def reqOR (vs : Vars) : Option Term → Kore.Pattern
  | none => .top KoreAML.R
  | some q => .equals (regSrtK Srt.bool) KoreAML.R (koreR vs q) (.dv (regSrtK Srt.bool) "true")

/-- `other` with the registry's names. -/
def otherR (W : FnOwise) (O : FnOther) : Kore.Pattern :=
  exs regSrtK O.vars
    (.and KoreAML.R [reqOR (W.ovs O) O.req, FnEqn.insR (W.ovs O) W.eqn.vars.length O.pats])

/-- `pattern` with the registry's names. -/
def patR (W : FnOwise) : Kore.Pattern :=
  .implies KoreAML.R
    (.and KoreAML.R [.not KoreAML.R (alts (W.others.map W.otherR)),
      .and KoreAML.R [match W.eqn.req with
        | none => .top KoreAML.R
        | some q => .equals (regSrtK Srt.bool) KoreAML.R (koreR W.eqn.av q) (.dv (regSrtK Srt.bool) "true"),
       FnEqn.insR W.eqn.av W.eqn.vars.length W.eqn.pats]])
    (.equals (regSrtK W.eqn.s) KoreAML.R (koreR W.eqn.av W.eqn.lhs)
      (.and (regSrtK W.eqn.s) [koreR W.eqn.av W.eqn.rhs, .top (regSrtK W.eqn.s)]))

/-- An other equation is over the registry's symbols and sorts. -/
def otherReg (O : FnOther) : Bool :=
  O.vars.all (fun p => decide (p.2 < nRegSorts)) && FnEqn.patsReg O.pats &&
  (match O.req with | none => true | some q => reg q)

/-- The `[owise]` equation is over the registry's symbols and sorts, each of its variables is free
in its pattern, and in the pattern's table `R`, its variables and each other equation's have
distinct places. -/
def regular (W : FnOwise) : Bool :=
  W.eqn.regular && W.others.all otherReg &&
  W.eqn.av.all (fun p => (KoreAML.freeOf [] W.patR).contains (.evar p.1 (regSrtK p.2))) &&
  W.others.all (apartIn (KoreAML.tableOf [KoreAML.Rv] W.patR) regSrtK W)

end FnOwise

/-! ## Valuations updated at the binders -/

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- The valuation `e` updated at each variable of the list, in order. -/
def fo_upd (e : Valuation M) : List (EVar × M) → Valuation M
  | [] => e
  | p :: ps => fo_upd (KoreAML.updE e p.1 p.2) ps

theorem fo_upd_out : ∀ (l : List (EVar × M)) (e : Valuation M) (y : EVar), y ∉ l.map Prod.fst →
    (fo_upd e l).evalEvar y = e.evalEvar y
  | [], _, _, _ => rfl
  | p :: ps, e, y, hy => by
    simp only [List.map_cons, List.mem_cons, not_or] at hy
    rw [fo_upd, fo_upd_out ps _ y hy.2]
    exact Function.update_noteq hy.1 _ _

theorem fo_upd_in : ∀ (l : List (EVar × M)) (e : Valuation M) (x : EVar) (a : M), (l.map Prod.fst).Nodup →
    (x, a) ∈ l → (fo_upd e l).evalEvar x = a
  | [], _, _, _, _, hx => absurd hx List.not_mem_nil
  | p :: ps, e, x, a, hn, hx => by
    rw [List.map_cons, List.nodup_cons] at hn
    rw [fo_upd]
    rcases List.mem_cons.mp hx with rfl | hx'
    · rw [fo_upd_out ps _ _ hn.1]
      exact Function.update_same _ _ _
    · exact fo_upd_in ps _ x a hn.2 hx'

/-- The binders of the variables `vs` at the table `t`, the i-th at the element `A (j + i)`. -/
def fo_binds (t : KoreAML.VarTable) (k : Srt → Kore.KSort) (A : Nat → M) : Nat → Vars → List (EVar × M)
  | _, [] => []
  | j, v :: vs => (t.ev (.evar v.1 (k v.2)), A j) :: fo_binds t k A (j + 1) vs

theorem fo_binds_fst (t : KoreAML.VarTable) (k : Srt → Kore.KSort) (A : Nat → M) :
    ∀ (j : Nat) (vs : Vars), (fo_binds t k A j vs).map Prod.fst = (FnOwise.keys k vs).map t.ev
  | _, [] => rfl
  | j, v :: vs => by
    rw [fo_binds, List.map_cons, fo_binds_fst t k A (j + 1) vs]
    rfl

theorem fo_binds_mem (t : KoreAML.VarTable) (k : Srt → Kore.KSort) (A : Nat → M) :
    ∀ (vs : Vars) (j i : Nat) (v : String × Srt), vs[i]? = some v →
      (t.ev (.evar v.1 (k v.2)), A (j + i)) ∈ fo_binds t k A j vs
  | [], _, _, _, hv => by simp at hv
  | w :: vs, j, 0, v, hv => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hv
    subst hv
    exact List.mem_cons_self ..
  | w :: vs, j, i + 1, v, hv => by
    simp only [List.getElem?_cons_succ] at hv
    have := fo_binds_mem t k A vs (j + 1) i v hv
    rw [show j + (i + 1) = j + 1 + i by omega]
    exact List.mem_cons_of_mem _ this

/-- `t.ev` is injective where `t.idxOf` is. -/
theorem fo_ev_inj {t : KoreAML.VarTable} {a b : KoreAML.VarKey} (h : t.ev a = t.ev b) : t.idxOf a = t.idxOf b := by
  unfold KoreAML.VarTable.ev KoreAML.VarTable.index at h
  have := congrArg EVar.val h
  simp only at this
  omega

theorem fo_ev_nodup {t : KoreAML.VarTable} {l : List KoreAML.VarKey} (h : (l.map t.idxOf).Nodup) :
    (l.map t.ev).Nodup := by
  have he : l.map t.ev = (l.map t.idxOf).map (fun n => (⟨n + 1⟩ : EVar)) := by
    rw [List.map_map]; rfl
  rw [he]
  exact List.Pairwise.map _ (fun a b hab heq => hab (by simp only [EVar.mk.injEq] at heq; omega)) h

theorem fo_ev_not_mem {t : KoreAML.VarTable} {x : KoreAML.VarKey} {l : List KoreAML.VarKey}
    (h : t.idxOf x ∉ l.map t.idxOf) : t.ev x ∉ l.map t.ev := by
  intro hx
  obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hx
  exact h (List.mem_map.mpr ⟨y, hy, fo_ev_inj hxy⟩)

end

/-! ## From values to the translated premise -/

/-- **The binders, at elements.** Where `A (j + i)` is an element of the sort of the i-th of the
variables `vs` and `body` holds at the valuation updated at their binders to those elements, the
binders around `body` hold. -/
theorem fo_exs_intro {M : Type} {I : Interpretation KoreAML.Sym M} (hD : KoreAML.DefOK I)
    (t : KoreAML.VarTable) (c : Semantics) (A : Nat → M) (body : Kore.Pattern) {m : M} :
    ∀ (vs : Vars) (j : Nat) (e : Valuation M),
      (∀ i v, vs[i]? = some v → ∀ e', (KoreAML.inhOf (KoreAML.trSort t (srtOf c v.2))).interpret I e' (A (j + i))) →
      (KoreAML.tr ⟨t, []⟩ body).interpret I (fo_upd e (fo_binds t (srtOf c) A j vs)) m →
      (KoreAML.tr ⟨t, []⟩ (FnOwise.exs (srtOf c) vs body)).interpret I e m
  | [], _, _, _, hb => hb
  | v :: vs, j, e, hA, hb => by
    rw [FnOwise.exs, KoreAML.tr, KoreAML.interp_sExists_elem hD]
    refine ⟨A j, hA 0 v rfl _, fo_exs_intro hD t c A body vs (j + 1) _ (fun i v' hv' e' => ?_) hb⟩
    have := hA (i + 1) v' hv' e'
    rwa [show j + (i + 1) = j + 1 + i by omega] at this

theorem fo_tr_or2 {ctx : KoreAML.Ctx} (S : Kore.KSort) (p q : Kore.Pattern) :
    KoreAML.tr ctx (.or S [p, q]) = KoreAML.sOr (KoreAML.trSort ctx.vars S) (KoreAML.tr ctx p) (KoreAML.tr ctx q) := by
  rw [KoreAML.tr]; simp only [KoreAML.trOrList]

/-- One alternative of `alts` that holds, at an element of the sort `R`, makes it hold. -/
theorem fo_alts_intro {M : Type} {I : Interpretation KoreAML.Sym M} {t : KoreAML.VarTable} {e : Valuation M}
    {a : M} (hRa : (KoreAML.inhOf (KoreAML.trSort t KoreAML.R)).interpret I e a) {p : Kore.Pattern}
    (hp : (KoreAML.tr ⟨t, []⟩ p).interpret I e a) :
    ∀ ps : List Kore.Pattern, p ∈ ps → (KoreAML.tr ⟨t, []⟩ (FnOwise.alts ps)).interpret I e a
  | [], hm => absurd hm List.not_mem_nil
  | q :: ps, hm => by
    rw [FnOwise.alts, fo_tr_or2, KoreAML.interp_sOr]
    refine ⟨hRa, ?_⟩
    rcases List.mem_cons.mp hm with rfl | hm'
    · exact Or.inl hp
    · exact Or.inr (fo_alts_intro hRa hp ps hm')

/-- The element of the value σ' gives the place `n + j`, the j-th binder's. -/
noncomputable def fo_A (c : Semantics) {M : Type} [Inhabited M] (I : Interpretation KoreAML.Sym M) (σ' : Subst)
    (n j : Nat) : M :=
  elemOf c I ((σ'.lookup (n + j)).getD default)

theorem fo_vkey_left (c : Semantics) {av ov : Vars} {i : Nat} (hi : i < av.length) :
    vkey c (av ++ ov) i = vkey c av i := by
  unfold vkey
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem fo_vkey_mem (c : Semantics) {av : Vars} {i : Nat} (hi : i < av.length) :
    vkey c av i ∈ FnOwise.keys (srtOf c) av := by
  unfold vkey FnOwise.keys
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.mem_map.mpr ⟨av[i], List.getElem_mem hi, rfl⟩

/-- **The valuation updated at the binders.** Where, in the table `t`, `R`, the equation's
variables `av` and an other equation's `ov` have distinct places: at the valuation updated at the
binders of `ov`, each to the element of its value under σ', every variable of `av ++ ov` is the
element of its value under σ' (σ' agreeing with σ on `av`), and `R` keeps its element. -/
theorem fo_hag_upd {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c)
    {av ov : Vars} {σ σ' : Subst} {t : KoreAML.VarTable} {e : Valuation M}
    (hag : ∀ i v, i < av.length → σ.lookup i = some v →
      ∀ m, m = e.evalEvar (t.ev (vkey c av i)) ↔ (den c v).interpret I e m)
    (hagr : ∀ i, i < av.length → σ'.lookup i = σ.lookup i)
    (hσ' : ∀ i p, (av ++ ov)[i]? = some p → ∃ v, σ'.lookup i = some v ∧ c.sortOf v = some p.2)
    (hap : ((KoreAML.sortVarKey KoreAML.Rv :: FnOwise.keys (srtOf c) (av ++ ov)).map t.idxOf).Nodup) :
    (∀ i v, i < (av ++ ov).length → σ'.lookup i = some v → ∀ m,
      m = (fo_upd e (fo_binds t (srtOf c) (fo_A c I σ' av.length) 0 ov)).evalEvar (t.ev (vkey c (av ++ ov) i)) ↔
        (den c v).interpret I (fo_upd e (fo_binds t (srtOf c) (fo_A c I σ' av.length) 0 ov)) m) ∧
    (fo_upd e (fo_binds t (srtOf c) (fo_A c I σ' av.length) 0 ov)).evalEvar (t.ev (.sortVar "R")) =
      e.evalEvar (t.ev (.sortVar "R")) := by
  generalize hA : fo_A c I σ' av.length = A
  rw [List.map_cons, List.nodup_cons, FnOwise.keys, List.map_append, List.map_append, List.nodup_append] at hap
  obtain ⟨hRn, hna, hno, hdis⟩ := hap
  have hfst := fo_binds_fst t (srtOf c) A 0 ov
  have hnf : ((fo_binds t (srtOf c) A 0 ov).map Prod.fst).Nodup := by
    rw [hfst]; exact fo_ev_nodup hno
  have hout : ∀ x, t.idxOf x ∉ (FnOwise.keys (srtOf c) ov).map t.idxOf →
      (fo_upd e (fo_binds t (srtOf c) A 0 ov)).evalEvar (t.ev x) = e.evalEvar (t.ev x) := by
    intro x hx
    refine fo_upd_out _ e _ ?_
    rw [hfst]
    exact fo_ev_not_mem hx
  refine ⟨fun i v hi hv m => ?_, hout _ fun hm => hRn (List.mem_append_right _ hm)⟩
  have hden : ∀ e', (den c v).interpret I e' m ↔ (den c v).interpret I e m :=
    fun e' => (den_closed c v).interp e' e m
  by_cases hil : i < av.length
  · rw [fo_vkey_left c hil, hden, ← hag i v hil ((hagr i hil).symm.trans hv) m]
    have hmem := fo_vkey_mem c hil
    rw [hout _ fun hm => hdis _ (List.mem_map.mpr ⟨_, hmem, rfl⟩) _ hm rfl]
  · have hj : i = av.length + (i - av.length) := by omega
    have hlt : i - av.length < ov.length := by rw [List.length_append] at hi; omega
    obtain ⟨p, hp⟩ : ∃ p, ov[i - av.length]? = some p := ⟨_, List.getElem?_eq_getElem hlt⟩
    have hp' : (av ++ ov)[i]? = some p := by
      rw [List.getElem?_append_right (by omega)]; exact hp
    obtain ⟨v', hv', hvs⟩ := hσ' i p hp'
    rw [hv] at hv'
    cases hv'
    have hk : vkey c (av ++ ov) i = .evar p.1 (srtOf c p.2) := by
      unfold vkey; rw [List.getD_eq_getElem?_getD, hp']; rfl
    have hin := fo_binds_mem t (srtOf c) A ov 0 (i - av.length) p hp
    rw [hk, fo_upd_in _ e _ _ hnf hin, ← hA, (elemOf_spec hI hvs _).1 m]
    unfold fo_A
    rw [Nat.zero_add, ← hj, hv]
    rfl

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
  (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) {vars : Vars} {σ : Subst} {tbl : KoreAML.VarTable} {e : Valuation M}
  (hσ : ∀ i p, vars[i]? = some p → ∃ v, σ.lookup i = some v ∧ c.sortOf v = some p.2)
  (hag : ∀ i v, i < vars.length → σ.lookup i = some v →
    ∀ m, m = e.evalEvar (tbl.ev (vkey c vars i)) ↔ (den c v).interpret I e m)
  {m : M} (hR : KoreAML.IsSort I (e.evalEvar (tbl.ev (.sortVar "R"))))
  (hRm : KoreAML.Inh I (e.evalEvar (tbl.ev (.sortVar "R"))) m)
include h hI hσ hag hR hRm

/-- **A `requires` with the value `true` holds** at an element of the sort `R`. -/
theorem fo_req_intro (q : Term) (hq : srt? c vars q = some Srt.bool) (hv : val c σ q = some (bool true)) :
    (KoreAML.tr ⟨tbl, []⟩ (.equals (srtOf c Srt.bool) KoreAML.R (kore c vars q)
      (.dv (srtOf c Srt.bool) "true"))).interpret I e m := by
  haveI : OvlOK c := ovlOK_of_core h
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e b ↔ b = e.evalEvar (tbl.ev (.sortVar "R")) :=
    fun b => by rw [trSort_R, KoreAML.interp_evar]
  obtain ⟨τb, hτbsort, hτb⟩ := srt_den hI
    (Nat.lt_of_lt_of_le (show Srt.bool < nRegSorts by decide) (Nat.le_add_right _ c.sortNames.length))
  rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (hτb tbl e) hRv hτbsort hR]
  refine ⟨hRm, fun b _ => ?_⟩
  rw [(den_val h hI hσ hag q hq).1 b, hv]
  show (den c (bool true)).interpret I e b ↔ _
  unfold den KoreAML.den bool
  rw [GroundTerm.kore]
  unfold srtOf
  rw [KoreAML.tr_dv, KoreAML.tr_dv]
  rfl

/-- **Patterns that match hold**: where each pattern has the value of its argument variable (and
its `#as` variable that value too), the `\in` premises hold at an element of the sort `R`. -/
theorem fo_ins_intro : ∀ (ps : List FnPat) (k : Nat), FnEqn.patsTyped c vars k ps = true →
    FnEqn.Matches c σ k ps → (KoreAML.tr ⟨tbl, []⟩ (FnEqn.ins c vars k ps)).interpret I e m
  | [], _, _, _ => by
    have hD := defOK hI
    rw [FnEqn.ins, show KoreAML.tr ⟨tbl, []⟩ (.top KoreAML.R) = KoreAML.sTop (KoreAML.trSort tbl KoreAML.R) from by
      rw [KoreAML.tr], KoreAML.interp_sTop hD isFree_R,
      KoreAML.interp_inhOf_of (fun b => by rw [trSort_R, KoreAML.interp_evar])]
    exact hRm
  | (s', u, as) :: ps, k, htp', hm => by
    haveI : OvlOK c := ovlOK_of_core h
    have hD := defOK hI
    have hc := sat_sigItem hI (sig_ceilDef (c := c))
    have hRv : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret I e b ↔ b = e.evalEvar (tbl.ev (.sortVar "R")) :=
      fun b => by rw [trSort_R, KoreAML.interp_evar]
    simp only [FnEqn.patsTyped, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at htp'
    obtain ⟨⟨⟨⟨hpR, hxk⟩, hpt⟩, has⟩, hrest⟩ := htp'
    obtain ⟨hmu, hmas, hm'⟩ := hm
    simp only [FnEqn.ins]
    rw [tr_and2, KoreAML.interp_sAnd]
    refine ⟨?_, fo_ins_intro ps (k + 1) hrest hm'⟩
    obtain ⟨τp, hτpsort, hτp⟩ := srt_den hI (Nat.lt_of_lt_of_le hpR (Nat.le_add_right _ c.sortNames.length))
    have hDk := den_val h hI hσ hag (.var k) hxk
    -- the value of the argument variable
    have hk : ∃ w, σ.lookup k = some w := by
      simp only [srt?] at hxk
      obtain ⟨p, hp, -⟩ := Option.map_eq_some_iff.mp hxk
      obtain ⟨w, hw, -⟩ := hσ k p hp
      exact ⟨w, hw⟩
    obtain ⟨w, hw⟩ := hk
    have hwv : val c σ (.var k) = some w := by rw [fq_val_var]; exact hw
    have hws := hDk.2 w hwv
    obtain ⟨hw1, hw2⟩ := elemOf_spec hI hws e
    have hφ : ∀ a', (KoreAML.tr ⟨tbl, []⟩ (kore c vars (.var k))).interpret I e a' → KoreAML.Inh I τp a' := by
      intro a' ha'
      rw [hDk.1, hwv] at ha'
      rw [(hw1 a').mp ha']
      refine (KoreAML.interp_inhOf_of (fun a'' => ?_)).mp hw2
      have := hτp tbl e a''
      rwa [trSort_srtOf_twoT] at this
    have hdw : ∀ (u' : Term), val c σ u' = some w → ∀ s'', srt? c vars u' = some s'' →
        (KoreAML.tr ⟨tbl, []⟩ (kore c vars u')).interpret I e (elemOf c I w) := by
      intro u' hu' s'' hs''
      rw [(den_val h hI hσ hag u' hs'').1, hu']
      exact (hw1 _).mpr rfl
    rw [KoreAML.tr, KoreAML.interp_sIn hD hc (hτp tbl e) hRv hτpsort hR hφ]
    refine ⟨⟨elemOf c I w, hdw (.var k) hwv s' hxk, ?_⟩, hRm⟩
    have hu : val c σ u = some w := hmu.trans hw
    cases as with
    | none =>
      simp only [FnEqn.patK]
      exact hdw u hu s' hpt
    | some j =>
      simp only [FnEqn.patK]
      rw [tr_and2, KoreAML.interp_sAnd]
      refine ⟨hdw u hu s' hpt, hdw (.var j) ?_ s' (eq_of_beq has)⟩
      rw [fq_val_var]
      exact (hmas j rfl).trans hw

end

/-! ## The `[owise]` equation entailed -/

/-- **A library equation in the function form with the `owise` premise that holds of the values is
entailed at values.** For a semantics meeting `coreOK` and an `[owise]` equation `W` with
`FnOwise.Holds`: the translation of any axiom declaration whose pattern is `W`'s, over the one sort
variable `R`, with each variable of the equation free in it and, in its table, `R`, the equation's
variables and each other equation's variables at distinct places, holds in every model of `Γ c` at
every valuation that sends the axiom's free element variables to values. -/
theorem FnEqn.entailed_owise {c : Semantics} (h : c.coreOK = true) (W : FnOwise) (ht : W.eqn.typed c = true)
    (hto : ∀ O ∈ W.others, W.otherTyped c O = true) (hE : W.Holds c) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = W.pattern c) (hsv : ad.ax.sortVars = [KoreAML.Rv])
    (hfv : ∀ i, i < W.eqn.av.length → vkey c W.eqn.av i ∈ KoreAML.freeOf [] ad.ax.pattern)
    (hap : ∀ O ∈ W.others, W.apartIn (KoreAML.tableOf ad.ax.sortVars ad.ax.pattern) (srtOf c) O = true) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat := by
  generalize hEq : W.eqn = E at ht hfv
  intro M _ I hI e hat m
  obtain ⟨hok, hsr, -, hg, -, -, -, -, hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  simp only [FnEqn.typed, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨⟨⟨⟨hsR, hvR⟩, htl⟩, htr⟩, htp⟩, htq⟩ := ht
  have hnum : ∀ {s : Srt}, s < nRegSorts → s < nRegSorts + c.sortNames.length :=
    fun hs => Nat.lt_of_lt_of_le hs (Nat.le_add_right _ _)
  obtain ⟨σ, hσ, hag⟩ := fq_subst h hI E.av hvR ad.ax hfv e hat
  unfold KoreAML.trAxiom
  dsimp only
  generalize htb : KoreAML.tableOf ad.ax.sortVars ad.ax.pattern = t at hag hap ⊢
  rw [interpret_impl]
  intro hgd
  have hR : KoreAML.IsSort I (e.evalEvar (t.ev (.sortVar "R"))) :=
    (KoreAML.interp_guard_sortVar hD).mp (conjList_mem hgd _ (List.mem_map.mpr ⟨.sortVar "R",
      List.mem_eraseDups.mpr (List.mem_append_left _ (by rw [hsv]; exact List.mem_singleton.mpr rfl)), rfl⟩))
  have hDV := fun (u : Term) (s : Srt) (hu : srt? c E.av u = some s) =>
    den_val (tbl := t) (e := e) h hI hσ hag u hu
  -- two terms of a sort that denote a common element have the same value
  have hsame : ∀ (u u' : Term) (s : Srt), srt? c E.av u = some s → srt? c E.av u' = some s → ∀ b,
      (KoreAML.tr ⟨t, []⟩ (kore c E.av u)).interpret I e b →
      (KoreAML.tr ⟨t, []⟩ (kore c E.av u')).interpret I e b → val c σ u = val c σ u' := by
    intro u u' s hu hu' b h1 h2
    rw [(hDV u s hu).1] at h1
    rw [(hDV u' s hu').1] at h2
    cases hv : val c σ u with
    | none => rw [hv] at h1; exact h1.elim
    | some w =>
      cases hv' : val c σ u' with
      | none => rw [hv'] at h2; exact h2.elim
      | some w' =>
        rw [hv] at h1
        rw [hv'] at h2
        have hw := (hDV u s hu).2 w hv
        have hw' := (hDV u' s hu').2 w' hv'
        exact congrArg some (values_apart hI hg hsc.trans (apartSort_of_sorted hg hw) hw hw'
          ((((elemOf_spec hI hw e).1 b).mp h1).symm.trans (((elemOf_spec hI hw' e).1 b).mp h2)))
  -- the sorts
  obtain ⟨τ, hτsort, hτ⟩ := srt_den hI (hnum hsR)
  obtain ⟨τb, hτbsort, hτb⟩ := srt_den hI (hnum (show Srt.bool < nRegSorts by decide))
  have hdist : (distinctSorts c).contains Srt.bool = true := by
    refine List.elem_eq_true_of_mem ?_
    unfold distinctSorts
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
  have hRv : ∀ b, (KoreAML.trSort t KoreAML.R).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "R")) :=
    fun b => by rw [trSort_R, KoreAML.interp_evar]
  -- the `\in` premises give the match
  have hmatch : ∀ (ps : List FnPat) (k : Nat) (a : M), FnEqn.patsTyped c E.av k ps = true →
      (KoreAML.tr ⟨t, []⟩ (FnEqn.ins c E.av k ps)).interpret I e a → FnEqn.Matches c σ k ps := by
    intro ps
    induction ps with
    | nil => intro k a _ _; trivial
    | cons p ps ih =>
      intro k a htp' hi
      obtain ⟨s', u, as⟩ := p
      simp only [FnEqn.patsTyped, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at htp'
      obtain ⟨⟨⟨⟨hpR, hxk⟩, hpt⟩, has⟩, hrest⟩ := htp'
      simp only [FnEqn.ins] at hi
      rw [tr_and2, KoreAML.interp_sAnd] at hi
      obtain ⟨hin, hi'⟩ := hi
      obtain ⟨τp, hτpsort, hτp⟩ := srt_den hI (hnum hpR)
      have hφ : ∀ a', (KoreAML.tr ⟨t, []⟩ (kore c E.av (.var k))).interpret I e a' → KoreAML.Inh I τp a' := by
        intro a' ha'
        rw [(hDV (.var k) s' hxk).1] at ha'
        cases hv : val c σ (.var k) with
        | none => rw [hv] at ha'; exact ha'.elim
        | some w =>
          rw [hv] at ha'
          have hw := (hDV (.var k) s' hxk).2 w hv
          obtain ⟨hw1, hw2⟩ := elemOf_spec hI hw e
          rw [(hw1 a').mp ha']
          refine (KoreAML.interp_inhOf_of (fun a'' => ?_)).mp hw2
          have := hτp t e a''
          rwa [trSort_srtOf_twoT] at this
      rw [KoreAML.tr, KoreAML.interp_sIn hD hc (hτp t e) hRv hτpsort hR hφ] at hin
      obtain ⟨⟨b, hxb, hpb⟩, -⟩ := hin
      cases as with
      | none =>
        simp only [FnEqn.patK] at hpb
        refine ⟨?_, fun j hj => (by cases hj), ih (k + 1) a hrest hi'⟩
        have := hsame u (.var k) s' hpt hxk b hpb hxb
        rwa [fq_val_var] at this
      | some j =>
        simp only [FnEqn.patK] at hpb
        rw [tr_and2, KoreAML.interp_sAnd] at hpb
        refine ⟨?_, fun j' hj' => ?_, ih (k + 1) a hrest hi'⟩
        · have := hsame u (.var k) s' hpt hxk b hpb.1 hxb
          rwa [fq_val_var] at this
        · cases hj'
          have := hsame (.var j) (.var k) s' (eq_of_beq has) hxk b hpb.2 hxb
          rwa [fq_val_var, fq_val_var] at this
  rw [hp]
  unfold FnOwise.pattern
  rw [hEq]
  simp only [KoreAML.sortOf]
  rw [KoreAML.interp_equal hD]
  intro a
  rw [KoreAML.tr, KoreAML.interp_sImp]
  constructor
  · exact fun h' => h'.1
  · intro ha
    refine ⟨ha, fun hprem => ?_⟩
    rw [tr_and2, KoreAML.interp_sAnd] at hprem
    obtain ⟨hown, hprem⟩ := hprem
    rw [tr_and2, KoreAML.interp_sAnd] at hprem
    obtain ⟨hprem, hins⟩ := hprem
    have hreq : ∀ q, E.req = some q → val c σ q = some (bool true) := by
      intro q hq
      unfold FnEqn.reqP at hprem
      rw [hq] at hprem htq
      dsimp only at hprem htq
      have htq' : srt? c E.av q = some Srt.bool := eq_of_beq htq
      rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (hτb t e) hRv hτbsort hR] at hprem
      have hT : c.sortOf (bool true) = some Srt.bool := rmS_sortOf_bool c true
      obtain ⟨hT1, hT2⟩ := elemOf_spec hI hT e
      have hinh : KoreAML.Inh I τb (elemOf c I (bool true)) := by
        refine (KoreAML.interp_inhOf_of (fun a' => ?_)).mp hT2
        have := hτb t e a'
        rwa [trSort_srtOf_twoT] at this
      have hq1 := (hprem.2 _ hinh).mpr (by
        show (KoreAML.tr ⟨t, []⟩ (.dv (srtOf c Srt.bool) "true")).interpret I e _
        have : (den c (bool true)).interpret I e (elemOf c I (bool true)) := (hT1 _).mpr rfl
        unfold den KoreAML.den bool at this
        rw [GroundTerm.kore] at this
        unfold srtOf
        rw [KoreAML.tr_dv] at this ⊢
        exact this)
      rw [(hDV q _ htq').1] at hq1
      cases hvq : val c σ q with
      | none => rw [hvq] at hq1; exact hq1.elim
      | some w =>
        rw [hvq] at hq1
        have hw := (hDV q _ htq').2 w hvq
        by_cases hne : w = bool true
        · rw [hne]
        · exact absurd ⟨hq1, (hT1 _).mpr rfl⟩
            (dom_apart hI hdist hw hT hne e _)
    -- the `owise` premise: no other equation applies
    have hRa : (KoreAML.inhOf (KoreAML.trSort t KoreAML.R)).interpret I e a := ha
    have hno : ∀ O ∈ W.others, ¬ (KoreAML.tr ⟨t, []⟩ (W.other c O)).interpret I e a := by
      intro O hO hO'
      unfold FnOwise.owiseP at hown
      rw [KoreAML.tr, KoreAML.interp_sNot] at hown
      exact hown.1 (fo_alts_intro hRa hO' _ (List.mem_map.mpr ⟨O, hO, rfl⟩))
    have how : ∀ O ∈ W.others, ∀ σ' : Subst, (∀ i, i < W.eqn.av.length → σ'.lookup i = σ.lookup i) →
        (∀ j p, O.vars[j]? = some p → ∃ v, σ'.lookup (W.eqn.av.length + j) = some v ∧ c.sortOf v = some p.2) →
        (∀ q, O.req = some q → val c σ' q = some (bool true)) →
        ¬ FnEqn.Matches c σ' W.eqn.vars.length O.pats := by
      rw [hEq]
      intro O hO σ' hagr hsrt hreq' hm'
      have hto' := hto O hO
      simp only [FnOwise.otherTyped, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hto'
      obtain ⟨⟨hoR, hopt⟩, hoq⟩ := hto'
      unfold FnOwise.ovs at hopt hoq
      rw [hEq] at hopt hoq
      have hap' := hap O hO
      unfold FnOwise.apartIn FnOwise.ovs at hap'
      rw [hEq, decide_eq_true_eq] at hap'
      have hσ' : ∀ i p, (E.av ++ O.vars)[i]? = some p → ∃ v, σ'.lookup i = some v ∧ c.sortOf v = some p.2 := by
        intro i p hp'
        by_cases hil : i < E.av.length
        · rw [List.getElem?_append_left hil] at hp'
          obtain ⟨v, hv, hvs⟩ := hσ i p hp'
          exact ⟨v, (hagr i hil).trans hv, hvs⟩
        · rw [List.getElem?_append_right (by omega)] at hp'
          obtain ⟨v, hv, hvs⟩ := hsrt _ p hp'
          rw [show E.av.length + (i - E.av.length) = i by omega] at hv
          exact ⟨v, hv, hvs⟩
      obtain ⟨hag', hRe⟩ := fo_hag_upd hI hag hagr hσ' hap'
      apply hno O hO
      unfold FnOwise.other FnOwise.ovs
      rw [hEq]
      refine fo_exs_intro hD t c (fo_A c I σ' E.av.length) _ O.vars 0 e (fun i p hp' e' => ?_) ?_
      · obtain ⟨v, hv, hvs⟩ := hsrt i p hp'
        have hvs' : c.sortOf ((σ'.lookup (E.av.length + (0 + i))).getD default) = some p.2 := by
          rw [Nat.zero_add, hv]; exact hvs
        have hnp : p.2 < nRegSorts := hoR p (List.mem_of_getElem? hp')
        obtain ⟨τp, -, hτp⟩ := srt_den hI (hnum hnp)
        refine (KoreAML.interp_inhOf_of (hτp t e')).mpr ?_
        refine (KoreAML.interp_inhOf_of (fun a'' => ?_)).mp (elemOf_spec hI hvs' e').2
        have := hτp t e' a''
        rwa [trSort_srtOf_twoT] at this
      · have hR' : KoreAML.IsSort I ((fo_upd e (fo_binds t (srtOf c) (fo_A c I σ' E.av.length) 0 O.vars)).evalEvar
            (t.ev (.sortVar "R"))) := by rw [hRe]; exact hR
        have hRm' : KoreAML.Inh I ((fo_upd e (fo_binds t (srtOf c) (fo_A c I σ' E.av.length) 0 O.vars)).evalEvar
            (t.ev (.sortVar "R"))) a := by rw [hRe]; exact (KoreAML.interp_inhOf_of hRv).mp ha
        rw [tr_and2, KoreAML.interp_sAnd]
        refine ⟨?_, fo_ins_intro h hI hσ' hag' hR' hRm' O.pats E.vars.length hopt hm'⟩
        cases hq : O.req with
        | none =>
          rw [FnOwise.reqO, show KoreAML.tr ⟨t, []⟩ (.top KoreAML.R) = KoreAML.sTop (KoreAML.trSort t KoreAML.R)
            from by rw [KoreAML.tr], KoreAML.interp_sTop hD isFree_R,
            KoreAML.interp_inhOf_of (fun b => by rw [trSort_R, KoreAML.interp_evar])]
          exact hRm'
        | some q =>
          rw [hq] at hoq
          exact fo_req_intro h hI hσ' hag' hR' hRm' q (eq_of_beq hoq) (hreq' q hq)
    have heq := hE σ (hEq ▸ hσ) (hEq ▸ hreq) (hEq ▸ hmatch E.pats E.vars.length a htp hins) how
    rw [hEq] at heq
    rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (hτ t e) hRv hτsort hR]
    refine ⟨(KoreAML.interp_inhOf_of hRv).mp ha, fun b hb => ?_⟩
    rw [(hDV E.lhs _ htl).1 b, heq, ← (hDV E.rhs _ htr).1 b, KoreAML.tr]
    show _ ↔ (KoreAML.sAnd (KoreAML.tr ⟨t, []⟩ (kore c E.av E.rhs))
      (KoreAML.tr ⟨t, []⟩ (.top (srtOf c E.s)))).interpret I e b
    rw [KoreAML.interp_sAnd, show KoreAML.tr ⟨t, []⟩ (.top (srtOf c E.s)) =
      KoreAML.sTop (KoreAML.trSort t (srtOf c E.s)) from by rw [KoreAML.tr]]
    rw [KoreAML.interp_sTop hD (by rw [trSort_srtOf_twoT]; rfl), KoreAML.interp_inhOf_of (hτ t e)]
    exact ⟨fun h' => ⟨h', hb⟩, And.left⟩


/-! ## Over the registry's names -/

namespace FnOwise

theorem exs_reg (c : Semantics) (p : Kore.Pattern) :
    ∀ vs : Vars, (∀ q ∈ vs, q.2 < nRegSorts) → exs (srtOf c) vs p = exs regSrtK vs p
  | [], _ => rfl
  | v :: vs, hv => by
    rw [exs, exs, srtOf_reg c (hv v (List.mem_cons_self ..)),
      exs_reg c p vs (fun q hq => hv q (List.mem_cons_of_mem _ hq))]

theorem keys_reg (c : Semantics) {vs : Vars} (hv : ∀ q ∈ vs, q.2 < nRegSorts) :
    keys (srtOf c) vs = keys regSrtK vs :=
  List.map_congr_left fun q hq => by rw [srtOf_reg c (hv q hq)]

theorem ovs_reg {W : FnOwise} {O : FnOther} (hE : W.eqn.regular = true) (hO : otherReg O = true) :
    ∀ q ∈ W.ovs O, q.2 < nRegSorts := by
  simp only [FnEqn.regular, otherReg, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hE hO
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact hE.1.1.1.1.1.2 q hq
  · exact hO.1.1 q hq

theorem other_reg (c : Semantics) {W : FnOwise} {O : FnOther} (hE : W.eqn.regular = true)
    (hO : otherReg O = true) : W.other c O = W.otherR O := by
  have hv := ovs_reg hE hO
  have hO' := hO
  simp only [otherReg, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hO'
  obtain ⟨⟨hov, hps⟩, hq⟩ := hO'
  unfold other otherR
  rw [exs_reg c _ O.vars hov, FnEqn.ins_reg c hv _ _ hps]
  congr 3
  cases hr : O.req with
  | none => rfl
  | some q =>
    rw [hr] at hq
    simp only [reqO, reqOR]
    rw [kore_reg c hv _ hq, srtOf_reg c (by decide : Srt.bool < nRegSorts)]

theorem pattern_reg (c : Semantics) {W : FnOwise} (hr : W.regular = true) : W.pattern c = W.patR := by
  simp only [regular, Bool.and_eq_true, List.all_eq_true] at hr
  obtain ⟨⟨⟨hE, hO⟩, -⟩, -⟩ := hr
  have hE' := hE
  simp only [FnEqn.regular, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hE'
  obtain ⟨⟨⟨⟨⟨⟨hs, hv⟩, hl⟩, hrr⟩, hps⟩, hq⟩, -⟩ := hE'
  have halts : W.others.map (W.other c) = W.others.map W.otherR :=
    List.map_congr_left fun O hO' => other_reg c hE (hO O hO')
  unfold pattern patR owiseP FnEqn.reqP
  rw [halts, kore_reg c hv _ hl, kore_reg c hv _ hrr, srtOf_reg c hs, FnEqn.ins_reg c hv _ _ hps]
  cases hreq : W.eqn.req with
  | none => rfl
  | some q =>
    rw [hreq] at hq
    dsimp only at hq ⊢
    rw [kore_reg c hv _ hq, srtOf_reg c (by decide : Srt.bool < nRegSorts)]

end FnOwise

/-- `FnEqn.entailed_owise` for an `[owise]` equation over the registry's names: the axiom's pattern
is compared with a pattern that does not depend on the semantics. -/
theorem FnEqn.entailed_owise_reg {c : Semantics} (h : c.coreOK = true) (W : FnOwise) (hr : W.regular = true)
    (ht : W.eqn.typed c = true) (hto : W.others.all (W.otherTyped c) = true) (hE : W.Holds c)
    (ad : KoreAML.AxiomDecl) (hp : ad.ax.pattern = W.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat := by
  have hr' := hr
  simp only [FnOwise.regular, Bool.and_eq_true, List.all_eq_true] at hr'
  obtain ⟨⟨⟨hEr, hOr⟩, hf⟩, hapR⟩ := hr'
  have hv : ∀ q ∈ W.eqn.av, q.2 < nRegSorts := by
    have := hEr
    simp only [FnEqn.regular, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at this
    exact this.1.1.1.1.1.2
  refine FnEqn.entailed_owise h W ht (fun O hO => List.all_eq_true.mp hto O hO) hE ad
    (hp.trans (FnOwise.pattern_reg c hr).symm) hsv (fun i hi => ?_) (fun O hO => ?_)
  · have hmem : W.eqn.av.getD i ("", 0) ∈ W.eqn.av := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      exact List.getElem_mem hi
    have := hf _ hmem
    rw [hp]
    unfold vkey
    rw [srtOf_reg c (hv _ hmem)]
    exact List.mem_of_elem_eq_true this
  · have := hapR O hO
    unfold FnOwise.apartIn at this ⊢
    rw [hp, hsv, FnOwise.keys_reg c (FnOwise.ovs_reg hEr (hOr O hO))]
    exact this

/-! ## domains.md 1915: `replace(Source, _, _, Count) => Source requires Count >=Int 0 [owise]` -/

/-- `replace(Source, _Gen0, _Gen1, Count) => Source requires Count >=Int 0`. -/
def fnReplaceEq : FnEqn :=
  ⟨[("VarSource", Srt.string), ("Var'Unds'Gen0", Srt.string), ("Var'Unds'Gen1", Srt.string),
      ("VarCount", Srt.int)], stringReplace,
    [(Srt.string, .var 0, none), (Srt.string, .var 1, none), (Srt.string, .var 2, none), (Srt.int, .var 3, none)],
    Srt.string, some (.app intGe [.var 3, intT 0]), .var 0⟩

/-- The other equation of `replace` (1911): its premise `Count >Int 0 andBool
findString(Source, ToReplace, 0) >=Int 0`, over the binders `_Gen5` (the count), `_Gen2`, `_Gen3`,
`_Gen4` (the three strings), at the places 8 to 11 after `fnReplaceEq`'s eight variables. -/
def fnReplaceOther : FnOther :=
  ⟨[("Var'Unds'Gen5", Srt.int), ("Var'Unds'Gen2", Srt.string), ("Var'Unds'Gen3", Srt.string),
      ("Var'Unds'Gen4", Srt.string)],
    [(Srt.string, .var 9, none), (Srt.string, .var 10, none), (Srt.string, .var 11, none), (Srt.int, .var 8, none)],
    some (.app boolAnd [.app intGt [.var 8, intT 0], .app intGe [.app stringFind [.var 9, .var 10, intT 0], intT 0]])⟩

/-- 1915, the `[owise]` equation of `replace`. -/
def fnReplaceOw : FnOwise := ⟨fnReplaceEq, [fnReplaceOther]⟩

section
variable {c : Semantics}

/-- A String value as a term's value. -/
def foS (a : String) : GroundTerm := .dv Srt.string (.tok a)

theorem fo_hv_intGt (x y : Int) : c.hv intGt [int x, int y] = some (bool (decide (x > y))) := hv_of_value rfl

theorem fo_hv_stringFind0 (a b : String) :
    c.hv stringFind [foS a, foS b, int 0] =
      some (int (KStr.firstOr ((KStr.positions a.toList).filter
        fun p => decide ((0 : Int) ≤ p) && KStr.occursAt b.toList a.toList p))) := by
  have hpos : KStr.isPos a.toList 0 = true := by simp [KStr.isPos]
  refine hv_of_value ?_
  show some ((KStr.find a.toList b.toList 0).map int) = _
  unfold KStr.find
  simp only [hpos, ↓reduceIte]
  rfl

theorem fo_hv_stringReplace (a b r : String) {k : Int} (hk : 0 ≤ k) :
    c.hv stringReplace [foS a, foS b, foS r, int k] =
      some (strV (KStr.replaceN b.toList r.toList k.toNat a.toList)) := by
  refine hv_of_value ?_
  show some ((KStr.replace a.toList b.toList r.toList k).map strV) = _
  unfold KStr.replace
  simp only [hk, ↓reduceIte]
  rfl

end

/-- Where the needle occurs at no position, replacing its occurrences leaves the string. -/
theorem fo_replaceN_none (n r : List Char) (s : List Char)
    (h : (KStr.positions s).filter (fun (p : Nat) => decide ((0 : Int) ≤ (p : Int)) && KStr.occursAt n s p) = []) :
    ∀ k, KStr.replaceN n r k s = s
  | 0 => rfl
  | k + 1 => by
    have hf : KStr.firstAt s n = none := by
      unfold KStr.firstAt
      rw [List.head?_eq_none_iff, List.filter_eq_nil_iff] at *
      intro p hp hocc
      exact h p hp (by simp [hocc])
    rw [KStr.replaceN, hf]

theorem fo_firstOr_nonneg : ∀ l : List Nat, l ≠ [] → 0 ≤ KStr.firstOr l
  | [], h => absurd rfl h
  | p :: _, _ => by show (0 : Int) ≤ (p : Int); omega

/-- **1915 holds of the values**: at a String `Source`, Strings `_Gen0`, `_Gen1` and an Int `Count`
with `Count >=Int 0`, where the other equation does not apply (`Count >Int 0` and the needle
occurs in `Source` do not both hold), `replace` is `Source`: either the count is 0 or the needle
occurs nowhere. -/
theorem fnReplaceOw_holds {c : Semantics} (hs : c.shapesOK = true) : fnReplaceOw.Holds c := by
  intro σ hσ hreq hm how
  obtain ⟨v0, hv0, hs0⟩ := hσ 0 _ rfl
  obtain ⟨v1, hv1, hs1⟩ := hσ 1 _ rfl
  obtain ⟨v2, hv2, hs2⟩ := hσ 2 _ rfl
  obtain ⟨v3, hv3, hs3⟩ := hσ 3 _ rfl
  obtain ⟨a, rfl⟩ := shape_string hs hs0
  obtain ⟨b, rfl⟩ := shape_string hs hs1
  obtain ⟨r, rfl⟩ := shape_string hs hs2
  obtain ⟨k, rfl⟩ := shape_int hs hs3
  obtain ⟨h4, -, h5, -, h6, -, h7, -, -⟩ := hm
  rw [fq_val_var] at h4 h5 h6 h7
  have h4' : σ.lookup 4 = some (foS a) := h4.symm.trans hv0
  have h5' : σ.lookup 5 = some (foS b) := h5.symm.trans hv1
  have h6' : σ.lookup 6 = some (foS r) := h6.symm.trans hv2
  have h7' : σ.lookup 7 = some (int k) := h7.symm.trans hv3
  have hq := hreq _ rfl
  simp only [val, valList, allSome, hv3, intT, dv_int, Option.bind_some, Option.map_some, fhv_intGe,
    Option.some.injEq] at hq
  have hk0 : 0 ≤ k := of_decide_eq_true (fq_bool_inj hq)
  -- the other equation does not apply
  have hnot : ¬ (k > 0 ∧ 0 ≤ KStr.firstOr ((KStr.positions a.toList).filter
      fun p => decide ((0 : Int) ≤ p) && KStr.occursAt b.toList a.toList p)) := by
    intro hyes
    let σ' : Subst := (8, int k) :: (9, foS a) :: (10, foS b) :: (11, foS r) :: σ
    have hagr : ∀ i, i < fnReplaceOw.eqn.av.length → σ'.lookup i = σ.lookup i := by
      intro i hi
      have hi' : i < 8 := hi
      simp only [σ', List.lookup_cons]
      have e8 : (i == 8) = false := by simp; omega
      have e9 : (i == 9) = false := by simp; omega
      have e10 : (i == 10) = false := by simp; omega
      have e11 : (i == 11) = false := by simp; omega
      simp only [e8, e9, e10, e11]
    have l8 : σ'.lookup 8 = some (int k) := rfl
    have l9 : σ'.lookup 9 = some (foS a) := rfl
    have l10 : σ'.lookup 10 = some (foS b) := rfl
    have l11 : σ'.lookup 11 = some (foS r) := rfl
    refine how fnReplaceOther (List.mem_singleton_self _) σ' hagr ?_ ?_ ?_
    · intro j p hp
      match j, hp with
      | 0, hp => cases hp; exact ⟨int k, rfl, hs3⟩
      | 1, hp => cases hp; exact ⟨foS a, rfl, hs0⟩
      | 2, hp => cases hp; exact ⟨foS b, rfl, hs1⟩
      | 3, hp => cases hp; exact ⟨foS r, rfl, hs2⟩
    · intro q hq'
      cases hq'
      simp only [val, valList, allSome, intT, dv_int, Option.bind_some, Option.map_some, l8, l9, l10,
        fo_hv_intGt, fo_hv_stringFind0, fhv_intGe, fhv_boolAnd, Option.some.injEq]
      have e1 : decide (k > 0) = true := decide_eq_true hyes.1
      have e2 : decide (KStr.firstOr ((KStr.positions a.toList).filter
          fun p => decide ((0 : Int) ≤ p) && KStr.occursAt b.toList a.toList p) ≥ 0) = true :=
        decide_eq_true hyes.2
      rw [e1, e2]
      rfl
    · have g4 : σ'.lookup 4 = some (foS a) := (hagr 4 (by decide)).trans h4'
      have g5 : σ'.lookup 5 = some (foS b) := (hagr 5 (by decide)).trans h5'
      have g6 : σ'.lookup 6 = some (foS r) := (hagr 6 (by decide)).trans h6'
      have g7 : σ'.lookup 7 = some (int k) := (hagr 7 (by decide)).trans h7'
      refine ⟨?_, (fun _ h => by cases h), ?_, (fun _ h => by cases h), ?_, (fun _ h => by cases h), ?_,
        (fun _ h => by cases h), trivial⟩
      · rw [fq_val_var, l9]; exact g4.symm
      · rw [fq_val_var, l10]; exact g5.symm
      · rw [fq_val_var, l11]; exact g6.symm
      · rw [fq_val_var, l8]; exact g7.symm
  fq_eval [fnReplaceOw, fnReplaceEq, h4', h5', h6', h7', hv0, fo_hv_stringReplace a b r hk0]
  have hrep : KStr.replaceN b.toList r.toList k.toNat a.toList = a.toList := by
    by_cases hk : k = 0
    · subst hk; rfl
    · refine fo_replaceN_none _ _ _ (Classical.byContradiction fun hne => hnot ⟨by omega, ?_⟩) _
      exact fo_firstOr_nonneg _ hne
  rw [hrep]
  unfold strV
  rw [String.ofList_toList]

theorem fnReplaceOw_ev {c : Semantics} (h : c.coreOK = true) (hs : c.shapesOK = true) (ad : KoreAML.AxiomDecl)
    (hp : ad.ax.pattern = fnReplaceOw.patR) (hsv : ad.ax.sortVars = [KoreAML.Rv]) :
    EntailsAtValues c ad (KoreAML.trAxiom [] [] ad).pat :=
  FnEqn.entailed_owise_reg h fnReplaceOw (by decide +kernel) (by rfl) (by rfl) (fnReplaceOw_holds hs) ad hp hsv

end LibEv

end KCore
