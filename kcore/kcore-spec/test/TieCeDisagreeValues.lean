/-
  The values, in every model of the reading, of the three functions whose existential clause has
  instances that disagree: h of e3-ml-eq-rhs-or, f of e3-eq-exists-ml-in-or and f of
  e3-eq-exists-ml-in-or-int. Run from the package root:
  `lake env lean -j1 test/TieCeDisagreeValues.lean`. Every statement is on the literal `defn` of its
  text, for every interpretation H, in every model of Γ (so in every model of `Γc = Γ ∪ Γcl`).

  Each of the three functions is not `total`, and the reader gives its one equation as one clause
  with existential variables (`existentialClause`), whose equation in Γ is
  `f(X) = (∃ē. (rhs ∧ ⊤ ∧ post)) ∧ ⊤`. That equation determines the function at a value: it holds the
  elements of the instances, two of them at most arguments. So the clause's match independence is
  false (the ties' `match_refuted`), and the value is determined all the same, as a set:
  - `Or.h_values`: the elements of Int in `h(n)` are the element of n and the element of `0 - n`
    (`rule h(X) => f(X) #Or g(X)`, `f(X) => X`, `g(X) => 0 -Int X`);
  - `InOr.f_values`: the elements of Bool in `f(b)` are the element of b and the element of `!b`
    (`rule f(X) => X #Or (#Exists B. (B #And {B #Equals notBool X}))`);
  - `InOrInt.f_values`: the elements of Int in `f(n)` are the element of n and the element of
    `n + 1` (`rule f(X) => X #Or (#Exists B. (B #And {B #Equals X +Int 1}))`).

  What is read of Γ, and nothing else: its equations of the functions named, as `fnItems` writes
  them (`gAx_shape`, kernel decisions on the literal; `Rd.eqn_read` reads one at the valuation of a
  value, connective by connective); the signature (definedness, the item of `⌈_⌉`, the sort); and
  of the domains each value one element of its sort and the graph of the one hooked symbol applied
  (`_-Int_` at `[0, n]`, `notBool_` at `[b]`, `_+Int_` at `[n, 1]`), which no sentence of the text
  states. The premise is Γ's clause, not the text's equation as written: the statements are through
  the reading.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieCeDisagreeValues

open KCore ML Faithful KoreAML

/-- The axioms of Γ's function equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

kernel_rfl fnItems_withHooks : ∀ (c : Semantics) (H : HookParams), fnItems (c.withHooks H) = fnItems c

/-! ## Reading an equation of Γ of a unary function over a sort `sn`, by hand -/

namespace Rd

/-- The sort. -/
def sS (sn : String) : Kore.KSort := srt sn
/-- The premise every equation here writes: `\top ∧ (X0 ∈ V0 ∧ \top)`. -/
def premP (sn : String) : Kore.Pattern :=
  .and KoreAML.R [.top KoreAML.R, .and KoreAML.R [.in (sS sn) KoreAML.R (ev "X0" (sS sn)) (ev "VarV0" (sS sn)), .top KoreAML.R]]
/-- An equation `prem → F(X0) = rhs ∧ \top` over the sort. -/
def eqnP (sn f : String) (rhs : Kore.Pattern) : Kore.Pattern :=
  .implies KoreAML.R (premP sn) (.equals (sS sn) KoreAML.R (ap f [ev "X0" (sS sn)]) (.and (sS sn) [rhs, .top (sS sn)]))
/-- The free variables of such an equation. -/
def freeP (sn : String) : List VarKey := [.sortVar "R", .evar "X0" (sS sn), .evar "VarV0" (sS sn)]
/-- The table's numbering: the sort variable R is 1, X0 is 2, V0 is 3. -/
def TabOK (sn : String) (t : VarTable) : Prop :=
  t.ev (.sortVar "R") = ⟨1⟩ ∧ t.ev (.evar "X0" (sS sn)) = ⟨2⟩ ∧ t.ev (.evar "VarV0" (sS sn)) = ⟨3⟩

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- The valuation the equations are read at: the sort variable R (variable 1) is the sort, every
other element variable the element m1. -/
def valAt (σI m1 : M) : Valuation M := ⟨Function.update (fun _ => m1) ⟨1⟩ σI, KoreAML.val0.evalSvar⟩

theorem valAt_1 (σI m1 : M) : (valAt σI m1).evalEvar ⟨1⟩ = σI := by
  simp [valAt]
theorem valAt_ne (σI m1 : M) {x : EVar} (h : x ≠ ⟨1⟩) : (valAt σI m1).evalEvar x = m1 := by
  simp [valAt, Function.update_noteq h]

variable {sn : String} {σI : M}

omit [Inhabited M] in
theorem sort_read (hσI1 : ∀ a, I.evalSymb (.sort ("Sort" ++ sn)) a ↔ a = σI) (t : VarTable) (e : Valuation M) (b : M) :
    (trSort t (sS sn)).interpret I e b ↔ b = σI := by
  unfold sS; rw [trSort_srt]; exact hσI1 b

theorem tr_ev (t : VarTable) (n : String) (s : Kore.KSort) : tr ⟨t, []⟩ (ev n s) = .evar (t.ev (.evar n s)) := rfl

theorem tr_ap1 (t : VarTable) (f n : String) (s : Kore.KSort) :
    tr ⟨t, []⟩ (ap f [ev n s]) = sym (.symbol f) ⬝ .evar (t.ev (.evar n s)) := by
  unfold ap; rw [tr_app0, trArgs_cons, trArgs_nil, tr_ev]

omit [Inhabited M] in
theorem top_read (hD : DefOK I) (hσI1 : ∀ a, I.evalSymb (.sort ("Sort" ++ sn)) a ↔ a = σI) (t : VarTable)
    (e : Valuation M) (m : M) : (tr ⟨t, []⟩ (.top (sS sn))).interpret I e m ↔ Inh I σI m := by
  rw [KoreAML.tr, interp_sTop hD (by unfold sS; rw [trSort_srt]; rfl), interp_inhOf_of (sort_read hσI1 t e)]

omit [Inhabited M] in
theorem or_read (hσI1 : ∀ a, I.evalSymb (.sort ("Sort" ++ sn)) a ↔ a = σI) (t : VarTable) (e : Valuation M)
    (p q : Kore.Pattern) (m : M) :
    (tr ⟨t, []⟩ (.or (sS sn) [p, q])).interpret I e m ↔
      Inh I σI m ∧ ((tr ⟨t, []⟩ p).interpret I e m ∨ (tr ⟨t, []⟩ q).interpret I e m) := by
  rw [KoreAML.tr]; simp only [trOrList]
  rw [interp_sOr, interp_inhOf_of (sort_read hσI1 t e)]

/-- `V ∈ q` for an element variable V of the sort: q holds V's element. -/
theorem in_read (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) (hσI1 : ∀ a, I.evalSymb (.sort ("Sort" ++ sn)) a ↔ a = σI)
    (hσI2 : IsSort I σI) (t : VarTable) (e : Valuation M) (n : String) (q : Kore.Pattern)
    (hx : Inh I σI (e.evalEvar (t.ev (.evar n (sS sn))))) (m : M) :
    (tr ⟨t, []⟩ (.in (sS sn) (sS sn) (ev n (sS sn)) q)).interpret I e m ↔
      (tr ⟨t, []⟩ q).interpret I e (e.evalEvar (t.ev (.evar n (sS sn)))) ∧ Inh I σI m := by
  rw [KoreAML.tr, tr_ev, interp_sIn hD hc (sort_read hσI1 t e) (sort_read hσI1 t e) hσI2 hσI2
    (fun a ha => by rw [interp_evar] at ha; rw [ha]; exact hx) m]
  constructor
  · rintro ⟨⟨a, ha, hq⟩, hm⟩
    rw [interp_evar] at ha; subst ha; exact ⟨hq, hm⟩
  · rintro ⟨hq, hm⟩
    exact ⟨⟨_, interp_evar.mpr rfl, hq⟩, hm⟩

theorem equals_read (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) (hσI1 : ∀ a, I.evalSymb (.sort ("Sort" ++ sn)) a ↔ a = σI)
    (hσI2 : IsSort I σI) (t : VarTable) (e : Valuation M) (p q : Kore.Pattern) (m : M) :
    (tr ⟨t, []⟩ (.equals (sS sn) (sS sn) p q)).interpret I e m ↔
      Inh I σI m ∧ ∀ a, Inh I σI a → ((tr ⟨t, []⟩ p).interpret I e a ↔ (tr ⟨t, []⟩ q).interpret I e a) := by
  rw [KoreAML.tr, interp_sEquals hD hc (sort_read hσI1 t e) (sort_read hσI1 t e) hσI2 hσI2]

omit [Inhabited M] in
/-- `∃ V:s. φ`: φ at some element of the sort for V. -/
theorem exist_read (hD : DefOK I) (hσI1 : ∀ a, I.evalSymb (.sort ("Sort" ++ sn)) a ↔ a = σI) (t : VarTable)
    (e : Valuation M) (n : String) (φ : Kore.Pattern) (m : M) :
    (tr ⟨t, []⟩ (.exist (sS sn) (evar n (sS sn)) φ)).interpret I e m ↔
      ∃ a, Inh I σI a ∧ (tr ⟨t, []⟩ φ).interpret I (updE e (t.ev (.evar n (sS sn))) a) m := by
  rw [KoreAML.tr]
  show (sExists (t.ev (.evar n (sS sn))) (trSort t (sS sn)) (tr ⟨t, []⟩ φ)).interpret I e m ↔ _
  rw [interp_sExists_elem hD]
  exact exists_congr fun a => and_congr_left' (interp_inhOf_of (sort_read hσI1 t _))

omit [Inhabited M] in
theorem and3_read (t : VarTable) (e : Valuation M) (S : Kore.KSort) (p q r : Kore.Pattern) (m : M) :
    (tr ⟨t, []⟩ (.and S [p, q, r])).interpret I e m ↔
      (tr ⟨t, []⟩ p).interpret I e m ∧ (tr ⟨t, []⟩ q).interpret I e m ∧ (tr ⟨t, []⟩ r).interpret I e m := by
  rw [interp_and (List.cons_ne_nil _ _)]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]

omit [Inhabited M] in
theorem and2_read (t : VarTable) (e : Valuation M) (S : Kore.KSort) (p q : Kore.Pattern) (m : M) :
    (tr ⟨t, []⟩ (.and S [p, q])).interpret I e m ↔
      (tr ⟨t, []⟩ p).interpret I e m ∧ (tr ⟨t, []⟩ q).interpret I e m := by
  rw [interp_and (List.cons_ne_nil _ _)]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]

/-- **An equation `prem → F(X0) = rhs ∧ \top` of Γ read at `valAt`**: where X0 and V0 are the
element m1 of the sort, `F(X0)` and `rhs` have the same elements of the sort. -/
theorem eqn_read (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat)
    (hσI1 : ∀ a, I.evalSymb (.sort ("Sort" ++ sn)) a ↔ a = σI) (hσI2 : IsSort I σI) {ad : Kore.Axiom} {f : String}
    {rhs : Kore.Pattern} (hp : ad.pattern = eqnP sn f rhs)
    (hfree : (ad.sortVars.map sortVarKey ++ freeOf [] ad.pattern).eraseDups = freeP sn)
    (htab : TabOK sn (tableOf ad.sortVars ad.pattern))
    (hT : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ad⟩).pat) (m1 : M) (hm1 : Inh I σI m1) (b : M) (hb : Inh I σI b) :
    ((sym (.symbol f) ⬝ .evar ⟨2⟩).interpret I (valAt σI m1) b ↔
      (tr ⟨tableOf ad.sortVars ad.pattern, []⟩ rhs).interpret I (valAt σI m1) b) := by
  have h := hT (valAt σI m1) m1
  unfold trAxiom at h
  dsimp only at h
  rw [hfree] at h
  generalize ht : tableOf ad.sortVars ad.pattern = t at h htab ⊢
  obtain ⟨h1, h2, h3⟩ := htab
  rw [hp] at h
  rw [interpret_impl] at h
  have hS : ∀ b, (trSort t (sS sn)).interpret I (valAt σI m1) b ↔ b = σI := sort_read hσI1 t _
  have hRv : ∀ b, (trSort t KoreAML.R).interpret I (valAt σI m1) b ↔ b = σI := fun b => by
    rw [trSort_R, KoreAML.interp_evar, h1, valAt_1]
  have h2v : (valAt σI m1).evalEvar (t.ev (.evar "X0" (sS sn))) = m1 := by rw [h2]; exact valAt_ne σI m1 (by decide)
  have h3v : (valAt σI m1).evalEvar (t.ev (.evar "VarV0" (sS sn))) = m1 := by rw [h3]; exact valAt_ne σI m1 (by decide)
  have hg : (conjList ((freeP sn).map (guardOf t))).interpret I (valAt σI m1) m1 := by
    unfold freeP
    simp only [List.map, conjList, interpret_conj]
    refine ⟨(interp_guard_sortVar hD).mpr (by rw [h1, valAt_1]; exact hσI2), ?_, ?_⟩
    · exact (interp_guard_evar hD).mpr (by rw [h2v]; exact (interp_inhOf_of hS).mpr hm1)
    · exact (interp_guard_evar hD).mpr (by rw [h3v]; exact (interp_inhOf_of hS).mpr hm1)
  have h4 := (interp_equal hD).mp (h hg) m1
  unfold eqnP at h4
  simp only [sortOf] at h4
  have h5 := h4.mpr ((interp_inhOf_of hRv).mpr hm1)
  rw [KoreAML.tr, interp_sImp] at h5
  have hprem : (tr ⟨t, []⟩ (premP sn)).interpret I (valAt σI m1) m1 := by
    have htop : (tr ⟨t, []⟩ (.top KoreAML.R)).interpret I (valAt σI m1) m1 := by
      rw [KoreAML.tr, interp_sTop hD (by rw [trSort_R, h1]; rfl), interp_inhOf_of hRv]; exact hm1
    unfold premP
    rw [and2_read]
    refine ⟨htop, ?_⟩
    rw [and2_read]
    refine ⟨?_, htop⟩
    rw [KoreAML.tr, tr_ev, tr_ev]
    exact (interp_sIn_evar_svin hD hc hS hRv hσI2 hσI2 (by rw [h2v]; exact hm1) m1).mpr ⟨h2v.trans h3v.symm, hm1⟩
  have h6 := h5.2 hprem
  rw [KoreAML.tr, interp_sEquals hD hc hS hRv hσI2 hσI2] at h6
  have h7 := h6.2 b hb
  rw [tr_ap1, h2, and2_read] at h7
  rw [h7, top_read hD hσI1]
  exact ⟨fun h => h.1, fun h => ⟨h, hb⟩⟩

end
end Rd

open Rd

/-! ## e3-ml-eq-rhs-or: h(n) -/

namespace Or

definition_of defn from "f2-examples/e3-ml-eq-rhs-or.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- h, the third function of the reading (`rule h(X) => f(X) #Or g(X)`). -/
def fH : Sym := 386

noncomputable def gAx (k : Nat) : Kore.Axiom := (fnAxioms c).getD k ⟨[], .top KoreAML.R, []⟩
local notation "sI" => sS "Int"
def vV : Kore.Pattern := ev "VarV0" sI
def vW : Kore.Pattern := ev "VarV1" sI
/-- The right side of Γ's equation of h: `∃V1. (V1 ∧ ⊤ ∧ (V1 ∈ f(V0) ∨ V1 ∈ g(V0)))`. -/
def rhsH : Kore.Pattern :=
  .exist sI (evar "VarV1" sI) (.and sI [vW, .top sI, .or sI [.in sI sI vW (ap "Lblf" [vV]), .in sI sI vW (ap "Lblg" [vV])]])

/-- Γ's equations of f, g and h: `f(X0) = V0`, `g(X0) = 0 -Int V0`, and h's existential clause. -/
theorem gAx_shape :
    (gAx 0).pattern = eqnP "Int" "Lblf" vV ∧
    (gAx 1).pattern = eqnP "Int" "Lblg" (ap "Lbl'Unds'-Int'Unds'" [.dv sI "0", vV]) ∧
    (gAx 2).pattern = eqnP "Int" "Lblh" rhsH := by decide +kernel
theorem gAx_free : ∀ k ∈ [0, 1, 2], ((gAx k).sortVars.map sortVarKey ++ freeOf [] (gAx k).pattern).eraseDups = freeP "Int" := by
  decide +kernel
theorem gAx_tab : ∀ k ∈ [0, 1, 2], TabOK "Int" (tableOf (gAx k).sortVars (gAx k).pattern) := by
  unfold TabOK; decide +kernel
theorem gAx_tab4 : (tableOf (gAx 2).sortVars (gAx 2).pattern).ev (.evar "VarV1" (sS "Int")) = ⟨4⟩ := by decide +kernel
theorem fnAx_len : 2 < (fnAxioms c).length := by decide +kernel
theorem gAx_mem (k : Nat) (hk : k ∈ [0, 1, 2]) : gAx k ∈ fnAxioms c := by
  have hk' : k < (fnAxioms c).length := by
    have : k ≤ 2 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega
    exact Nat.lt_of_le_of_lt this fnAx_len
  unfold gAx
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some]
  exact List.getElem_mem hk'
theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl
theorem gAx_sat (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H))
    (k : Nat) (hk : k ∈ [0, 1, 2]) : I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", gAx k⟩).pat :=
  hI _ (Or.inl (Or.inl (Or.inr (Or.inl ⟨_, by rw [fnItems_withHooks, fnItems_eq]; exact List.mem_map_of_mem (gAx_mem k hk), rfl⟩))))

theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")
theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
theorem sub_name (H : HookParams) : (cH H).symName intSub = "Lbl'Unds'-Int'Unds'" ∧ instDecode? "Lbl'Unds'-Int'Unds'" = none :=
  (by decide +kernel : c.symName intSub = "Lbl'Unds'-Int'Unds'" ∧ instDecode? "Lbl'Unds'-Int'Unds'" = none)
theorem h_name (H : HookParams) : (cH H).symName fH = "Lblh" ∧ instDecode? "Lblh" = none :=
  (by decide +kernel : c.symName fH = "Lblh" ∧ instDecode? "Lblh" = none)
theorem den_int0 (H : HookParams) : den (cH H) (KCore.int 0) = KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt") := by
  show den c (KCore.int 0) = _; decide +kernel

/-- **h(n) in every model of the reading, for every H**: the elements of Int in `h(n)` are the
element of n and the element of `0 - n`. Γ's equation of h is its existential clause,
`h(X) = ∃V. (V ∧ (V ∈ f(X) ∨ V ∈ g(X)))`; Γ's equations of f and g give `f(n)` the element of n and
`g(n)` the elements of `0 -Int n`, which the graph of `_-Int_` at `[0, n]` makes the element of
`0 - n`. -/
theorem h_values (H : HookParams) (n : Int) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M) :
    ∃ σI, (∀ a, I.evalSymb (.sort "SortInt") a ↔ a = σI) ∧ ∀ m, Inh I σI m →
      ((KoreAML.den (symApp (cH H) fH (GroundTerm.koreList (cH H) [KCore.int n]))).interpret I e m ↔
        ((den (cH H) (KCore.int n)).interpret I e m ∨ (den (cH H) (KCore.int (0 - n))).interpret I e m)) := by
  have hD := defOK hI
  have hc : I ⊧ᴵ ceilDefItem.pat := sat_sigItem hI (sig_ceilDef (c := cH H))
  have hDom : I ⊧ᴵP ΓDomains (cH H) := fun φ hφ => sat_dom hI hφ
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σI, hσI1, hσI2⟩ := sortSing hI (int_numbered H)
  rw [int_name] at hσI1
  refine ⟨σI, hσI1, fun m hm => ?_⟩
  have hSI : ∀ (e : Valuation M) b, (sortP "Int").interpret I e b ↔ b = σI := fun _ b => hσI1 b
  obtain ⟨m1, hm1d, hm1s⟩ := TieRhs.den_single_dom hD hDom (show (cH H).sortOf (KCore.int n) = some Srt.int from rfl) KoreAML.val0
  obtain ⟨mN, hmNd, hmNs⟩ := TieRhs.den_single_dom hD hDom (show (cH H).sortOf (KCore.int (0 - n)) = some Srt.int from rfl) KoreAML.val0
  rw [int_name] at hm1s hmNs
  have hm1 : Inh I σI m1 := (interp_inhOf_of (hSI _)).mp hm1s
  have hmN : Inh I σI mN := (interp_inhOf_of (hSI _)).mp hmNs
  let e1 := valAt σI m1
  have hden1 : ∀ (e : Valuation M) b, (den (cH H) (KCore.int n)).interpret I e b ↔ b = m1 := fun e b =>
    ((den_closed (cH H) (KCore.int n)).interp e KoreAML.val0 b).trans (hm1d b)
  have hdenN : ∀ (e : Valuation M) b, (den (cH H) (KCore.int (0 - n))).interpret I e b ↔ b = mN := fun e b =>
    ((den_closed (cH H) (KCore.int (0 - n))).interp e KoreAML.val0 b).trans (hmNd b)
  have hev : ∀ k : Nat, k ≠ 1 → e1.evalEvar ⟨k⟩ = m1 := fun k hk => valAt_ne σI m1 (fun h => hk (by cases h; rfl))
  have htb := gAx_tab
  -- f(n) is n
  have hA := eqn_read hD hc hσI1 hσI2 gAx_shape.1 (gAx_free 0 (by decide)) (htb 0 (by decide)) (gAx_sat H hI 0 (by decide)) m1 hm1
  have hf : ∀ b, Inh I σI b → ((sym (.symbol "Lblf") ⬝ .evar ⟨2⟩).interpret I e1 b ↔ b = m1) := fun b hb => by
    rw [hA b hb]; unfold vV; rw [tr_ev, (htb 0 (by decide)).2.2, interp_evar, hev 3 (by decide)]
  -- g(n) is 0 - n
  have hB := eqn_read hD hc hσI1 hσI2 gAx_shape.2.1 (gAx_free 1 (by decide)) (htb 1 (by decide)) (gAx_sat H hI 1 (by decide)) m1 hm1
  have hg : ∀ b, Inh I σI b → ((sym (.symbol "Lblg") ⬝ .evar ⟨2⟩).interpret I e1 b ↔ b = mN) := fun b hb => by
    rw [hB b hb]
    have hgraph := hDom _ (Or.inl ⟨⟨intSub, [Srt.int, Srt.int], Srt.int⟩, [KCore.int 0, KCore.int n], some (KCore.int (0 - n)),
      by decide +kernel, rfl, rfl, fun h => absurd h (by simp), rfl⟩)
    have hg2 := (KoreAML.interp_equal hD).mp (hgraph e1 default)
    have h1 : tr ⟨tableOf (gAx 1).sortVars (gAx 1).pattern, []⟩ (ap "Lbl'Unds'-Int'Unds'" [.dv sI "0", vV]) =
        (KoreAML.sym (.symbol "Lbl'Unds'-Int'Unds'") ⬝ (KoreAML.sym (.dv "0") ⬝ KoreAML.sym (.sort "SortInt"))) ⬝ .evar ⟨3⟩ := by
      unfold ap vV; rw [tr_app0, trArgs_cons, trArgs_cons, trArgs_nil, tr_ev, (htb 1 (by decide)).2.2]; rfl
    have h2 : KoreAML.den (symApp (cH H) intSub (GroundTerm.koreList (cH H) [KCore.int 0, KCore.int n])) =
        (KoreAML.sym (.symbol "Lbl'Unds'-Int'Unds'") ⬝ den (cH H) (KCore.int 0)) ⬝ den (cH H) (KCore.int n) := by
      rw [symApp_noInst (c := cH H) (f := intSub) (by rw [(sub_name H).1]; exact (sub_name H).2), (sub_name H).1]; rfl
    rw [h1, ← hdenN e1 b, ← hg2 b, h2]
    exact interp_app_congr (fun m => interp_app_congr (fun _ => Iff.rfl) (fun m => by rw [den_int0]) m)
      (fun m => by rw [interp_evar, hev 3 (by decide), hden1]) b
  -- h(n) holds the elements of f(n) and of g(n)
  have hC := eqn_read hD hc hσI1 hσI2 gAx_shape.2.2 (gAx_free 2 (by decide)) (htb 2 (by decide)) (gAx_sat H hI 2 (by decide)) m1 hm1
  have t3 := (htb 2 (by decide)).2.2
  have hsw : ∀ (g : String) (e' : Valuation M), e'.evalEvar ⟨3⟩ = m1 → ∀ b,
      (sym (.symbol g) ⬝ .evar ⟨3⟩).interpret I e' b ↔ (sym (.symbol g) ⬝ .evar ⟨2⟩).interpret I e1 b :=
    fun g e' h3 b => interp_app_congr (e := e') (e' := e1) (φ := sym (.symbol g)) (φ' := sym (.symbol g))
      (ψ := .evar ⟨3⟩) (ψ' := .evar ⟨2⟩) (fun _ => Iff.rfl)
      (fun m => by rw [interp_evar, interp_evar, h3, hev 2 (by decide)]) b
  have hh : (sym (.symbol "Lblh") ⬝ .evar ⟨2⟩).interpret I e1 m ↔ (m = m1 ∨ m = mN) := by
    rw [hC m hm]
    unfold rhsH
    rw [exist_read hD hσI1]
    show (∃ a, Inh I σI a ∧ (tr ⟨_, []⟩ _).interpret I (updE e1 ((tableOf (gAx 2).sortVars (gAx 2).pattern).ev (.evar "VarV1" (sS "Int"))) a) m) ↔ _
    rw [gAx_tab4]
    have hu4 : ∀ a, (updE e1 ⟨4⟩ a).evalEvar ⟨4⟩ = a := fun a => by simp
    have hu3 : ∀ a, (updE e1 ⟨4⟩ a).evalEvar ⟨3⟩ = m1 := fun a => by
      show Function.update e1.evalEvar ⟨4⟩ a ⟨3⟩ = m1
      rw [Function.update_noteq (by decide)]; exact hev 3 (by decide)
    have hbody : ∀ a, Inh I σI a →
        ((tr ⟨tableOf (gAx 2).sortVars (gAx 2).pattern, []⟩ (.and sI [vW, .top sI,
            .or sI [.in sI sI vW (ap "Lblf" [vV]), .in sI sI vW (ap "Lblg" [vV])]])).interpret I (updE e1 ⟨4⟩ a) m ↔
          m = a ∧ (a = m1 ∨ a = mN)) := by
      intro a ha
      have hx : Inh I σI ((updE e1 ⟨4⟩ a).evalEvar ((tableOf (gAx 2).sortVars (gAx 2).pattern).ev (.evar "VarV1" (sS "Int")))) := by
        rw [gAx_tab4, hu4]; exact ha
      unfold vW vV
      rw [and3_read, tr_ev, gAx_tab4, interp_evar, hu4, top_read hD hσI1, or_read hσI1,
        in_read hD hc hσI1 hσI2 _ _ _ _ hx, in_read hD hc hσI1 hσI2 _ _ _ _ hx, tr_ap1, tr_ap1, gAx_tab4, t3, hu4,
        hsw _ _ (hu3 a), hsw _ _ (hu3 a), hf a ha, hg a ha]
      constructor
      · rintro ⟨h1, -, -, h2 | h2⟩
        · exact ⟨h1, Or.inl h2.1⟩
        · exact ⟨h1, Or.inr h2.1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, hm, hm, h2.imp (fun h => ⟨h, hm⟩) (fun h => ⟨h, hm⟩)⟩
    constructor
    · rintro ⟨a, ha, hb⟩
      obtain ⟨h1, h2⟩ := (hbody a ha).mp hb
      rw [h1]; exact h2
    · intro h
      exact ⟨m, hm, (hbody m hm).mpr ⟨rfl, h⟩⟩
  have h2 : KoreAML.den (symApp (cH H) fH (GroundTerm.koreList (cH H) [KCore.int n])) =
      KoreAML.sym (.symbol "Lblh") ⬝ den (cH H) (KCore.int n) := by
    rw [symApp_noInst (c := cH H) (f := fH) (by rw [(h_name H).1]; exact (h_name H).2), (h_name H).1]; rfl
  rw [h2, hden1, hdenN, ← hh]
  exact interp_app_congr (e := e) (e' := e1) (φ' := sym (.symbol "Lblh")) (ψ' := .evar ⟨2⟩) (fun _ => Iff.rfl)
    (fun m => (hden1 e m).trans (by rw [interp_evar, hev 2 (by decide)])) m

end Or

/-! ## e3-eq-exists-ml-in-or: f(b) -/

namespace InOr

definition_of defn from "f2-examples/e3-eq-exists-ml-in-or.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- f, the first function of the reading (`rule f(X) => X #Or (#Exists B. (B #And {B #Equals notBool X}))`). -/
def fF : Sym := 384

noncomputable def gAx (k : Nat) : Kore.Axiom := (fnAxioms c).getD k ⟨[], .top KoreAML.R, []⟩
local notation "sB" => sS "Bool"
def vV : Kore.Pattern := ev "VarV0" sB
def vB : Kore.Pattern := ev "VarV1" sB
def vW : Kore.Pattern := ev "VarV2" sB
/-- The body of the right side of Γ's equation of f:
`V2 ∧ ⊤ ∧ (V2 ∈ V0 ∨ (V2 ∈ V1 ∧ V1 = notBool V0))`. -/
def bodyF : Kore.Pattern :=
  .and sB [vW, .top sB, .or sB [.in sB sB vW vV,
    .and sB [.in sB sB vW vB, .equals sB sB vB (ap "LblnotBool'Unds'" [vV])]]]
/-- The right side of Γ's equation of f: `∃V1. ∃V2. bodyF`. -/
def rhsF : Kore.Pattern := .exist sB (evar "VarV1" sB) (.exist sB (evar "VarV2" sB) bodyF)

theorem gAx_shape : (gAx 0).pattern = eqnP "Bool" "Lblf" rhsF := by decide +kernel
theorem gAx_free : ((gAx 0).sortVars.map sortVarKey ++ freeOf [] (gAx 0).pattern).eraseDups = freeP "Bool" := by
  decide +kernel
theorem gAx_tab : TabOK "Bool" (tableOf (gAx 0).sortVars (gAx 0).pattern) := by
  unfold TabOK; decide +kernel
theorem gAx_tab4 : (tableOf (gAx 0).sortVars (gAx 0).pattern).ev (.evar "VarV1" (sS "Bool")) = ⟨4⟩ ∧
    (tableOf (gAx 0).sortVars (gAx 0).pattern).ev (.evar "VarV2" (sS "Bool")) = ⟨5⟩ := by decide +kernel
theorem fnAx_len : 0 < (fnAxioms c).length := by decide +kernel
theorem gAx_mem : gAx 0 ∈ fnAxioms c := by
  unfold gAx
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem fnAx_len, Option.getD_some]
  exact List.getElem_mem fnAx_len
theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl
theorem gAx_sat (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H)) :
    I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", gAx 0⟩).pat :=
  hI _ (Or.inl (Or.inl (Or.inr (Or.inl ⟨_, by rw [fnItems_withHooks, fnItems_eq]; exact List.mem_map_of_mem gAx_mem, rfl⟩))))

theorem bool_name (H : HookParams) : (cH H).sortName Srt.bool = "Bool" := (by decide +kernel : c.sortName Srt.bool = "Bool")
theorem bool_numbered (H : HookParams) : Srt.bool < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.bool < nRegSorts + c.sortNames.length)
theorem not_name (H : HookParams) : (cH H).symName boolNot = "LblnotBool'Unds'" ∧ instDecode? "LblnotBool'Unds'" = none :=
  (by decide +kernel : c.symName boolNot = "LblnotBool'Unds'" ∧ instDecode? "LblnotBool'Unds'" = none)
theorem f_name (H : HookParams) : (cH H).symName fF = "Lblf" ∧ instDecode? "Lblf" = none :=
  (by decide +kernel : c.symName fF = "Lblf" ∧ instDecode? "Lblf" = none)

/-- **f(b) in every model of the reading, for every H**: the elements of Bool in `f(b)` are the
element of b and the element of `notBool b`. Γ's equation of f is its existential clause,
`f(X) = ∃B. ∃V. (V ∧ (V ∈ X ∨ (V ∈ B ∧ B = notBool X)))`, and the graph of `notBool_` at `[b]`
makes `notBool b` the element of `!b`. -/
theorem f_values (H : HookParams) (b : Bool) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M) :
    ∃ σI, (∀ a, I.evalSymb (.sort "SortBool") a ↔ a = σI) ∧ ∀ m, Inh I σI m →
      ((KoreAML.den (symApp (cH H) fF (GroundTerm.koreList (cH H) [KCore.bool b]))).interpret I e m ↔
        ((den (cH H) (KCore.bool b)).interpret I e m ∨ (den (cH H) (KCore.bool (!b))).interpret I e m)) := by
  have hD := defOK hI
  have hc : I ⊧ᴵ ceilDefItem.pat := sat_sigItem hI (sig_ceilDef (c := cH H))
  have hDom : I ⊧ᴵP ΓDomains (cH H) := fun φ hφ => sat_dom hI hφ
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σI, hσI1, hσI2⟩ := sortSing hI (bool_numbered H)
  rw [bool_name] at hσI1
  refine ⟨σI, hσI1, fun m hm => ?_⟩
  have hSI : ∀ (e : Valuation M) x, (sortP "Bool").interpret I e x ↔ x = σI := fun _ x => hσI1 x
  obtain ⟨m1, hm1d, hm1s⟩ := TieRhs.den_single_dom hD hDom (show (cH H).sortOf (KCore.bool b) = some Srt.bool from rfl) KoreAML.val0
  obtain ⟨mN, hmNd, hmNs⟩ := TieRhs.den_single_dom hD hDom (show (cH H).sortOf (KCore.bool (!b)) = some Srt.bool from rfl) KoreAML.val0
  rw [bool_name] at hm1s hmNs
  have hm1 : Inh I σI m1 := (interp_inhOf_of (hSI _)).mp hm1s
  have hmN : Inh I σI mN := (interp_inhOf_of (hSI _)).mp hmNs
  let e1 := valAt σI m1
  have hden1 : ∀ (e : Valuation M) x, (den (cH H) (KCore.bool b)).interpret I e x ↔ x = m1 := fun e x =>
    ((den_closed (cH H) (KCore.bool b)).interp e KoreAML.val0 x).trans (hm1d x)
  have hdenN : ∀ (e : Valuation M) x, (den (cH H) (KCore.bool (!b))).interpret I e x ↔ x = mN := fun e x =>
    ((den_closed (cH H) (KCore.bool (!b))).interp e KoreAML.val0 x).trans (hmNd x)
  have hev : ∀ k : Nat, k ≠ 1 → e1.evalEvar ⟨k⟩ = m1 := fun k hk => valAt_ne σI m1 (fun h => hk (by cases h; rfl))
  have t3 := gAx_tab.2.2
  have t4 := gAx_tab4.1
  have t5 := gAx_tab4.2
  -- notBool at an element valuation giving V0 the element of b: the element of !b
  have hnot : ∀ (e' : Valuation M), e'.evalEvar ⟨3⟩ = m1 → ∀ x,
      ((sym (.symbol "LblnotBool'Unds'") ⬝ .evar ⟨3⟩).interpret I e' x ↔ x = mN) := by
    intro e' h3 x
    have hgraph := hDom _ (Or.inl ⟨⟨boolNot, [Srt.bool], Srt.bool⟩, [KCore.bool b], some (KCore.bool (!b)),
      by decide +kernel, rfl, by cases b <;> rfl, fun h => absurd h (by simp), rfl⟩)
    have hg2 := (KoreAML.interp_equal hD).mp (hgraph e' default)
    have h2 : KoreAML.den (symApp (cH H) boolNot (GroundTerm.koreList (cH H) [KCore.bool b])) =
        KoreAML.sym (.symbol "LblnotBool'Unds'") ⬝ den (cH H) (KCore.bool b) := by
      rw [symApp_noInst (c := cH H) (f := boolNot) (by rw [(not_name H).1]; exact (not_name H).2), (not_name H).1]; rfl
    rw [← hdenN e' x, ← hg2 x, h2]
    exact interp_app_congr (e := e') (e' := e') (φ' := sym (.symbol "LblnotBool'Unds'")) (ψ' := den (cH H) (KCore.bool b))
      (fun _ => Iff.rfl) (fun y => by rw [interp_evar, h3, hden1]) x
  have hC := eqn_read hD hc hσI1 hσI2 gAx_shape gAx_free gAx_tab (gAx_sat H hI) m1 hm1
  have hh : (sym (.symbol "Lblf") ⬝ .evar ⟨2⟩).interpret I e1 m ↔ (m = m1 ∨ m = mN) := by
    rw [hC m hm]
    unfold rhsF
    rw [exist_read hD hσI1, t4]
    have hbody : ∀ a w, Inh I σI a → Inh I σI w →
        ((tr ⟨tableOf (gAx 0).sortVars (gAx 0).pattern, []⟩ bodyF).interpret I (updE (updE e1 ⟨4⟩ a) ⟨5⟩ w) m ↔
          m = w ∧ (w = m1 ∨ (w = a ∧ a = mN))) := by
      intro a w ha hw
      have hu5 : (updE (updE e1 ⟨4⟩ a) ⟨5⟩ w).evalEvar ⟨5⟩ = w := by simp
      have hu4 : (updE (updE e1 ⟨4⟩ a) ⟨5⟩ w).evalEvar ⟨4⟩ = a := by
        show Function.update (Function.update e1.evalEvar ⟨4⟩ a) ⟨5⟩ w ⟨4⟩ = a
        rw [Function.update_noteq (by decide), Function.update_same]
      have hu3 : (updE (updE e1 ⟨4⟩ a) ⟨5⟩ w).evalEvar ⟨3⟩ = m1 := by
        show Function.update (Function.update e1.evalEvar ⟨4⟩ a) ⟨5⟩ w ⟨3⟩ = m1
        rw [Function.update_noteq (by decide), Function.update_noteq (by decide)]; exact hev 3 (by decide)
      have hx : Inh I σI ((updE (updE e1 ⟨4⟩ a) ⟨5⟩ w).evalEvar
          ((tableOf (gAx 0).sortVars (gAx 0).pattern).ev (.evar "VarV2" (sS "Bool")))) := by
        rw [t5, hu5]; exact hw
      unfold bodyF vW vB vV
      rw [and3_read, tr_ev, t5, interp_evar, hu5, top_read hD hσI1, or_read hσI1,
        in_read hD hc hσI1 hσI2 _ _ _ _ hx, and2_read, in_read hD hc hσI1 hσI2 _ _ _ _ hx,
        equals_read hD hc hσI1 hσI2, tr_ev, tr_ev, tr_ap1, t3, t4, t5, hu5, interp_evar, interp_evar, hu3, hu4]
      constructor
      · rintro ⟨h1, -, -, h2 | h2⟩
        · exact ⟨h1, Or.inl h2.1⟩
        · refine ⟨h1, Or.inr ⟨h2.1.1, ?_⟩⟩
          have h3 := (h2.2.2 a ha).mp (interp_evar.mpr hu4.symm)
          exact (hnot _ hu3 a).mp h3
      · rintro ⟨h1, h2⟩
        refine ⟨h1, hm, hm, ?_⟩
        rcases h2 with h2 | ⟨h2, h3⟩
        · exact Or.inl ⟨h2, hm⟩
        · refine Or.inr ⟨⟨h2, hm⟩, hm, fun x _ => ?_⟩
          rw [interp_evar, hu4, hnot _ hu3 x, h3]
    constructor
    · rintro ⟨a, ha, hb⟩
      rw [exist_read hD hσI1, t5] at hb
      obtain ⟨w, hw, hb⟩ := hb
      obtain ⟨h1, h2⟩ := (hbody a w ha hw).mp hb
      rw [h1]
      rcases h2 with h2 | ⟨h2, h3⟩
      · exact Or.inl h2
      · exact Or.inr (h2.trans h3)
    · intro h
      rcases h with h | h
      · refine ⟨m1, hm1, ?_⟩
        rw [exist_read hD hσI1, t5]
        exact ⟨m, hm, (hbody m1 m hm1 hm).mpr ⟨rfl, Or.inl h⟩⟩
      · refine ⟨mN, hmN, ?_⟩
        rw [exist_read hD hσI1, t5]
        exact ⟨m, hm, (hbody mN m hmN hm).mpr ⟨rfl, Or.inr ⟨h, rfl⟩⟩⟩
  have h2 : KoreAML.den (symApp (cH H) fF (GroundTerm.koreList (cH H) [KCore.bool b])) =
      KoreAML.sym (.symbol "Lblf") ⬝ den (cH H) (KCore.bool b) := by
    rw [symApp_noInst (c := cH H) (f := fF) (by rw [(f_name H).1]; exact (f_name H).2), (f_name H).1]; rfl
  rw [h2, hden1, hdenN, ← hh]
  exact interp_app_congr (e := e) (e' := e1) (φ' := sym (.symbol "Lblf")) (ψ' := .evar ⟨2⟩) (fun _ => Iff.rfl)
    (fun m => (hden1 e m).trans (by rw [interp_evar, hev 2 (by decide)])) m

end InOr

/-! ## e3-eq-exists-ml-in-or-int: f(n) -/

namespace InOrInt

definition_of defn from "f2-examples/e3-eq-exists-ml-in-or-int.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- f, the one function of the reading (`rule f(X) => X #Or (#Exists B. (B #And {B #Equals X +Int 1}))`). -/
def fF : Sym := 384

noncomputable def gAx (k : Nat) : Kore.Axiom := (fnAxioms c).getD k ⟨[], .top KoreAML.R, []⟩
local notation "sI" => sS "Int"
def vV : Kore.Pattern := ev "VarV0" sI
def vW : Kore.Pattern := ev "VarV1" sI
def vB : Kore.Pattern := ev "VarV2" sI
/-- `V0 +Int 1`. -/
def plusP : Kore.Pattern := ap "Lbl'UndsPlus'Int'Unds'" [vV, .dv sI "1"]
/-- The second alternative under its binder: `V1 ∈ V2 ∧ V2 = V0 +Int 1`. -/
def altF : Kore.Pattern := .and sI [.in sI sI vW vB, .equals sI sI vB plusP]
/-- The body of the right side of Γ's equation of f:
`V1 ∧ ⊤ ∧ (V1 ∈ V0 ∨ ∃V2. (V1 ∈ V2 ∧ V2 = V0 +Int 1))`. -/
def bodyF : Kore.Pattern :=
  .and sI [vW, .top sI, .or sI [.in sI sI vW vV, .exist sI (evar "VarV2" sI) altF]]
/-- The right side of Γ's equation of f: `∃V1. bodyF`. -/
def rhsF : Kore.Pattern := .exist sI (evar "VarV1" sI) bodyF

theorem gAx_shape : (gAx 0).pattern = eqnP "Int" "Lblf" rhsF := by decide +kernel
theorem gAx_free : ((gAx 0).sortVars.map sortVarKey ++ freeOf [] (gAx 0).pattern).eraseDups = freeP "Int" := by
  decide +kernel
theorem gAx_tab : TabOK "Int" (tableOf (gAx 0).sortVars (gAx 0).pattern) := by
  unfold TabOK; decide +kernel
theorem gAx_tab4 : (tableOf (gAx 0).sortVars (gAx 0).pattern).ev (.evar "VarV1" (sS "Int")) = ⟨4⟩ ∧
    (tableOf (gAx 0).sortVars (gAx 0).pattern).ev (.evar "VarV2" (sS "Int")) = ⟨5⟩ := by decide +kernel
theorem fnAx_len : 0 < (fnAxioms c).length := by decide +kernel
theorem gAx_mem : gAx 0 ∈ fnAxioms c := by
  unfold gAx
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem fnAx_len, Option.getD_some]
  exact List.getElem_mem fnAx_len
theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl
theorem gAx_sat (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ (cH H)) :
    I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", gAx 0⟩).pat :=
  hI _ (Or.inl (Or.inl (Or.inr (Or.inl ⟨_, by rw [fnItems_withHooks, fnItems_eq]; exact List.mem_map_of_mem gAx_mem, rfl⟩))))

theorem int_name (H : HookParams) : (cH H).sortName Srt.int = "Int" := (by decide +kernel : c.sortName Srt.int = "Int")
theorem int_numbered (H : HookParams) : Srt.int < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : Srt.int < nRegSorts + c.sortNames.length)
theorem add_name (H : HookParams) : (cH H).symName intAdd = "Lbl'UndsPlus'Int'Unds'" ∧ instDecode? "Lbl'UndsPlus'Int'Unds'" = none :=
  (by decide +kernel : c.symName intAdd = "Lbl'UndsPlus'Int'Unds'" ∧ instDecode? "Lbl'UndsPlus'Int'Unds'" = none)
theorem f_name (H : HookParams) : (cH H).symName fF = "Lblf" ∧ instDecode? "Lblf" = none :=
  (by decide +kernel : c.symName fF = "Lblf" ∧ instDecode? "Lblf" = none)
theorem den_int1 (H : HookParams) : den (cH H) (KCore.int 1) = KoreAML.sym (.dv "1") ⬝ KoreAML.sym (.sort "SortInt") := by
  show den c (KCore.int 1) = _; decide +kernel

/-- **f(n) in every model of the reading, for every H**: the elements of Int in `f(n)` are the
element of n and the element of `n + 1`. Γ's equation of f is its existential clause,
`f(X) = ∃V. (V ∧ (V ∈ X ∨ ∃B. (V ∈ B ∧ B = X +Int 1)))`, and the graph of `_+Int_` at `[n, 1]`
makes `n +Int 1` the element of `n + 1`. -/
theorem f_values (H : HookParams) (n : Int) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP Γ (cH H)) (e : Valuation M) :
    ∃ σI, (∀ a, I.evalSymb (.sort "SortInt") a ↔ a = σI) ∧ ∀ m, Inh I σI m →
      ((KoreAML.den (symApp (cH H) fF (GroundTerm.koreList (cH H) [KCore.int n]))).interpret I e m ↔
        ((den (cH H) (KCore.int n)).interpret I e m ∨ (den (cH H) (KCore.int (n + 1))).interpret I e m)) := by
  have hD := defOK hI
  have hc : I ⊧ᴵ ceilDefItem.pat := sat_sigItem hI (sig_ceilDef (c := cH H))
  have hDom : I ⊧ᴵP ΓDomains (cH H) := fun φ hφ => sat_dom hI hφ
  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)
  obtain ⟨σI, hσI1, hσI2⟩ := sortSing hI (int_numbered H)
  rw [int_name] at hσI1
  refine ⟨σI, hσI1, fun m hm => ?_⟩
  have hSI : ∀ (e : Valuation M) x, (sortP "Int").interpret I e x ↔ x = σI := fun _ x => hσI1 x
  obtain ⟨m1, hm1d, hm1s⟩ := TieRhs.den_single_dom hD hDom (show (cH H).sortOf (KCore.int n) = some Srt.int from rfl) KoreAML.val0
  obtain ⟨mN, hmNd, hmNs⟩ := TieRhs.den_single_dom hD hDom (show (cH H).sortOf (KCore.int (n + 1)) = some Srt.int from rfl) KoreAML.val0
  rw [int_name] at hm1s hmNs
  have hm1 : Inh I σI m1 := (interp_inhOf_of (hSI _)).mp hm1s
  have hmN : Inh I σI mN := (interp_inhOf_of (hSI _)).mp hmNs
  let e1 := valAt σI m1
  have hden1 : ∀ (e : Valuation M) x, (den (cH H) (KCore.int n)).interpret I e x ↔ x = m1 := fun e x =>
    ((den_closed (cH H) (KCore.int n)).interp e KoreAML.val0 x).trans (hm1d x)
  have hdenN : ∀ (e : Valuation M) x, (den (cH H) (KCore.int (n + 1))).interpret I e x ↔ x = mN := fun e x =>
    ((den_closed (cH H) (KCore.int (n + 1))).interp e KoreAML.val0 x).trans (hmNd x)
  have hev : ∀ k : Nat, k ≠ 1 → e1.evalEvar ⟨k⟩ = m1 := fun k hk => valAt_ne σI m1 (fun h => hk (by cases h; rfl))
  have t3 := gAx_tab.2.2
  have t4 := gAx_tab4.1
  have t5 := gAx_tab4.2
  -- `V0 +Int 1` at a valuation giving V0 the element of n: the element of n + 1
  have hplus : ∀ (e' : Valuation M), e'.evalEvar ⟨3⟩ = m1 → ∀ x,
      ((tr ⟨tableOf (gAx 0).sortVars (gAx 0).pattern, []⟩ plusP).interpret I e' x ↔ x = mN) := by
    intro e' h3 x
    have hgraph := hDom _ (Or.inl ⟨⟨intAdd, [Srt.int, Srt.int], Srt.int⟩, [KCore.int n, KCore.int 1], some (KCore.int (n + 1)),
      by decide +kernel, rfl, rfl, fun h => absurd h (by simp), rfl⟩)
    have hg2 := (KoreAML.interp_equal hD).mp (hgraph e' default)
    have h1 : tr ⟨tableOf (gAx 0).sortVars (gAx 0).pattern, []⟩ plusP =
        (KoreAML.sym (.symbol "Lbl'UndsPlus'Int'Unds'") ⬝ .evar ⟨3⟩) ⬝ (KoreAML.sym (.dv "1") ⬝ KoreAML.sym (.sort "SortInt")) := by
      unfold plusP ap vV; rw [tr_app0, trArgs_cons, trArgs_cons, trArgs_nil, tr_ev, t3]; rfl
    have h2 : KoreAML.den (symApp (cH H) intAdd (GroundTerm.koreList (cH H) [KCore.int n, KCore.int 1])) =
        (KoreAML.sym (.symbol "Lbl'UndsPlus'Int'Unds'") ⬝ den (cH H) (KCore.int n)) ⬝ den (cH H) (KCore.int 1) := by
      rw [symApp_noInst (c := cH H) (f := intAdd) (by rw [(add_name H).1]; exact (add_name H).2), (add_name H).1]; rfl
    rw [h1, ← hdenN e' x, ← hg2 x, h2]
    exact interp_app_congr (e := e') (e' := e')
      (fun y => interp_app_congr (e := e') (e' := e') (φ' := KoreAML.sym (.symbol "Lbl'UndsPlus'Int'Unds'"))
        (ψ' := den (cH H) (KCore.int n)) (fun _ => Iff.rfl) (fun z => by rw [interp_evar, h3, hden1]) y)
      (fun y => by rw [den_int1]) x
  have hC := eqn_read hD hc hσI1 hσI2 gAx_shape gAx_free gAx_tab (gAx_sat H hI) m1 hm1
  have hh : (sym (.symbol "Lblf") ⬝ .evar ⟨2⟩).interpret I e1 m ↔ (m = m1 ∨ m = mN) := by
    rw [hC m hm]
    unfold rhsF
    rw [exist_read hD hσI1, t4]
    have hu3 : ∀ a, (updE e1 ⟨4⟩ a).evalEvar ⟨3⟩ = m1 := fun a => by
      show Function.update e1.evalEvar ⟨4⟩ a ⟨3⟩ = m1
      rw [Function.update_noteq (by decide)]; exact hev 3 (by decide)
    have hu4 : ∀ a, (updE e1 ⟨4⟩ a).evalEvar ⟨4⟩ = a := fun a => by simp
    -- the second alternative under its binder
    have halt : ∀ a w, Inh I σI a → Inh I σI w →
        ((tr ⟨tableOf (gAx 0).sortVars (gAx 0).pattern, []⟩ altF).interpret I (updE (updE e1 ⟨4⟩ a) ⟨5⟩ w) m ↔
          a = w ∧ w = mN) := by
      intro a w ha hw
      have hv5 : (updE (updE e1 ⟨4⟩ a) ⟨5⟩ w).evalEvar ⟨5⟩ = w := by simp
      have hv4 : (updE (updE e1 ⟨4⟩ a) ⟨5⟩ w).evalEvar ⟨4⟩ = a := by
        show Function.update (Function.update e1.evalEvar ⟨4⟩ a) ⟨5⟩ w ⟨4⟩ = a
        rw [Function.update_noteq (by decide), Function.update_same]
      have hv3 : (updE (updE e1 ⟨4⟩ a) ⟨5⟩ w).evalEvar ⟨3⟩ = m1 := by
        show Function.update (Function.update e1.evalEvar ⟨4⟩ a) ⟨5⟩ w ⟨3⟩ = m1
        rw [Function.update_noteq (by decide)]; exact hu3 a
      have hx : Inh I σI ((updE (updE e1 ⟨4⟩ a) ⟨5⟩ w).evalEvar
          ((tableOf (gAx 0).sortVars (gAx 0).pattern).ev (.evar "VarV1" (sS "Int")))) := by
        rw [t4, hv4]; exact ha
      unfold altF vW vB
      rw [and2_read, in_read hD hc hσI1 hσI2 _ _ _ _ hx, equals_read hD hc hσI1 hσI2, tr_ev, t4, t5,
        interp_evar, hv4, hv5]
      constructor
      · rintro ⟨⟨h1, -⟩, -, h2⟩
        refine ⟨h1, ?_⟩
        exact (hplus _ hv3 w).mp ((h2 w hw).mp (interp_evar.mpr hv5.symm))
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1, hm⟩, hm, fun x _ => ?_⟩
        rw [interp_evar, hv5, hplus _ hv3 x, h2]
    have hbody : ∀ a, Inh I σI a →
        ((tr ⟨tableOf (gAx 0).sortVars (gAx 0).pattern, []⟩ bodyF).interpret I (updE e1 ⟨4⟩ a) m ↔
          m = a ∧ (a = m1 ∨ a = mN)) := by
      intro a ha
      have hx : Inh I σI ((updE e1 ⟨4⟩ a).evalEvar ((tableOf (gAx 0).sortVars (gAx 0).pattern).ev (.evar "VarV1" (sS "Int")))) := by
        rw [t4, hu4]; exact ha
      unfold bodyF vW vV
      rw [and3_read, tr_ev, t4, interp_evar, hu4, top_read hD hσI1, or_read hσI1,
        in_read hD hc hσI1 hσI2 _ _ _ _ hx, tr_ev, t3, t4, hu4, interp_evar, hu3, exist_read hD hσI1, t5]
      constructor
      · rintro ⟨h1, -, -, h2 | ⟨w, hw, h2⟩⟩
        · exact ⟨h1, Or.inl h2.1⟩
        · obtain ⟨h3, h4⟩ := (halt a w ha hw).mp h2
          exact ⟨h1, Or.inr (h3.trans h4)⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, hm, hm, ?_⟩
        rcases h2 with h2 | h2
        · exact Or.inl ⟨h2, hm⟩
        · exact Or.inr ⟨mN, hmN, (halt a mN ha hmN).mpr ⟨h2, rfl⟩⟩
    constructor
    · rintro ⟨a, ha, hb⟩
      obtain ⟨h1, h2⟩ := (hbody a ha).mp hb
      rw [h1]; exact h2
    · intro h
      exact ⟨m, hm, (hbody m hm).mpr ⟨rfl, h⟩⟩
  have h2 : KoreAML.den (symApp (cH H) fF (GroundTerm.koreList (cH H) [KCore.int n])) =
      KoreAML.sym (.symbol "Lblf") ⬝ den (cH H) (KCore.int n) := by
    rw [symApp_noInst (c := cH H) (f := fF) (by rw [(f_name H).1]; exact (f_name H).2), (f_name H).1]; rfl
  rw [h2, hden1, hdenN, ← hh]
  exact interp_app_congr (e := e) (e' := e1) (φ' := sym (.symbol "Lblf")) (ψ' := .evar ⟨2⟩) (fun _ => Iff.rfl)
    (fun m => (hden1 e m).trans (by rw [interp_evar, hev 2 (by decide)])) m

end InOrInt

end KCore.TieCeDisagreeValues

#print axioms KCore.TieCeDisagreeValues.Or.h_values
#print axioms KCore.TieCeDisagreeValues.InOr.f_values
#print axioms KCore.TieCeDisagreeValues.InOrInt.f_values
