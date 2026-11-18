/-
  KCore. The variables a term holds under a set of symbols, and what a model gives them.

  `occsUnder c H t` lists the variables t holds under constructors, injections and the symbols H
  names. `heldOccs` is the test at `Semantics.holds` (`heldOccs_eq`) and `ctorOccs` the test at no
  symbol (`ctorOccs_eq`), so one induction serves both.

  - `HeldBack c I f k`: what the induction needs of a symbol H names, with the signature k a right
    side's context gives it: its application is written with its own name, and where a value's
    element is what it gives on elements of its argument sorts, those elements are values' of
    those sorts.
  - `occsUnder_witnessed`: in a model of `Γ`, if the element of a value of a well-sorted right
    side's sort lies in its translation, at a valuation of its variables in their sorts, the
    valuation gives each variable of `occsUnder c H t` the element of a value of its sort, for
    every H whose symbols have `HeldBack`.
  - `collHeld`: the unit, element and concatenation symbols of the collections, the symbols
    `Semantics.holds` names (`holds_eq_collHeld`). Such a symbol is no overloading symbol
    (`collHeld_not_ovl`), a right side's context gives it the signature a left side's context gives
    it (`held_lookup`), and it has `HeldBack` (`collHeld_back`).
  - `ovl_backR`: an overloading symbol with no function among its overloads has `HeldBack`.
  - `mem_elem`: where `V ∈ t` holds at some element, the valuation's element at V is in t's
    translation.
-/
import KcoreSpec.RhsValues

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace KCore

open ML Faithful
open KoreAML (DefOK Inh IsSort Closed VarKey VarTable)

/-! ## The occurrence test over a set of symbols -/

mutual
  /-- The variables a term holds under constructors, injections and the symbols H names. -/
  def occsUnder (c : Semantics) (H : Sym → Bool) : Term → List Nat
    | .var i => [i]
    | .app f ts => if c.isCtor f || H f then occsUnderList c H ts else []
    | .inj _ _ t => occsUnder c H t
    | .as t i => occsUnder c H t ++ [i]
    | .dv _ _ => []
  def occsUnderList (c : Semantics) (H : Sym → Bool) : List Term → List Nat
    | [] => []
    | t :: ts => occsUnder c H t ++ occsUnderList c H ts
end

mutual
  /-- The landed `heldOccs` is the test at `Semantics.holds`. -/
  theorem heldOccs_eq (c : Semantics) : ∀ t : Term, heldOccs c t = occsUnder c c.holds t
    | .var _ => by rw [heldOccs, occsUnder]
    | .dv _ _ => by rw [heldOccs, occsUnder]
    | .app f ts => by rw [heldOccs, occsUnder, heldOccsList_eq c ts]
    | .inj _ _ t => by rw [heldOccs, occsUnder, heldOccs_eq c t]
    | .as t i => by rw [heldOccs, occsUnder, heldOccs_eq c t]
  theorem heldOccsList_eq (c : Semantics) : ∀ ts : List Term, heldOccsList c ts = occsUnderList c c.holds ts
    | [] => by rw [heldOccsList, occsUnderList]
    | t :: ts => by rw [heldOccsList, occsUnderList, heldOccs_eq c t, heldOccsList_eq c ts]
end

mutual
  /-- The landed `ctorOccs` is the test at no symbol. -/
  theorem ctorOccs_eq (c : Semantics) : ∀ t : Term, ctorOccs c t = occsUnder c (fun _ => false) t
    | .var _ => by rw [ctorOccs, occsUnder]
    | .dv _ _ => by rw [ctorOccs, occsUnder]
    | .app f ts => by rw [ctorOccs, occsUnder, ctorOccsList_eq c ts, Bool.or_false]
    | .inj _ _ t => by rw [ctorOccs, occsUnder, ctorOccs_eq c t]
    | .as t i => by rw [ctorOccs, occsUnder, ctorOccs_eq c t]
  theorem ctorOccsList_eq (c : Semantics) : ∀ ts : List Term, ctorOccsList c ts = occsUnderList c (fun _ => false) ts
    | [] => by rw [ctorOccsList, occsUnderList]
    | t :: ts => by rw [ctorOccsList, occsUnderList, ctorOccs_eq c t, ctorOccsList_eq c ts]
end

mutual
  /-- More symbols hold more variables. -/
  theorem occsUnder_mono (c : Semantics) {H H' : Sym → Bool} (hH : ∀ f, H f = true → H' f = true) :
      ∀ (t : Term), ∀ i ∈ occsUnder c H t, i ∈ occsUnder c H' t
    | .var _, i, hi => by rw [occsUnder] at hi ⊢; exact hi
    | .dv _ _, i, hi => by rw [occsUnder] at hi; cases hi
    | .app f ts, i, hi => by
      rw [occsUnder] at hi ⊢
      split at hi
      · rename_i h
        have h' : (c.isCtor f || H' f) = true := by
          rcases Bool.or_eq_true_iff.mp h with h | h
          · rw [h]; rfl
          · rw [hH f h, Bool.or_true]
        rw [if_pos h']
        exact occsUnderList_mono c hH ts i hi
      · cases hi
    | .inj _ _ t, i, hi => by rw [occsUnder] at hi ⊢; exact occsUnder_mono c hH t i hi
    | .as t j, i, hi => by
      rw [occsUnder] at hi ⊢
      rcases List.mem_append.mp hi with hi | hi
      · exact List.mem_append_left _ (occsUnder_mono c hH t i hi)
      · exact List.mem_append_right _ hi
  theorem occsUnderList_mono (c : Semantics) {H H' : Sym → Bool} (hH : ∀ f, H f = true → H' f = true) :
      ∀ (ts : List Term), ∀ i ∈ occsUnderList c H ts, i ∈ occsUnderList c H' ts
    | [], i, hi => by rw [occsUnderList] at hi; cases hi
    | t :: ts, i, hi => by
      rw [occsUnderList] at hi ⊢
      rcases List.mem_append.mp hi with hi | hi
      · exact List.mem_append_left _ (occsUnder_mono c hH t i hi)
      · exact List.mem_append_right _ (occsUnderList_mono c hH ts i hi)
end

/-- The unit, element and concatenation symbols of the collections: a pattern hook or a collection
pattern symbol. -/
def collHeld (c : Semantics) (f : Sym) : Bool := patternHooks.contains f || c.isCollPat f

/-- `Semantics.holds` names the `collHeld` symbols. -/
theorem holds_eq_collHeld (c : Semantics) (f : Sym) : c.holds f = collHeld c f := rfl

/-! ## The variables held under a set of symbols, at a value -/

/-- **What `occsUnder_witnessed` needs of a held symbol**, with the signature k the right side's context gives it:
its application is written with its own name, and if a value's element is what it gives on
elements of its argument sorts, those elements are values' of those sorts. -/
def HeldBack (c : Semantics) {M : Type} [Inhabited M] (I : Interpretation KoreAML.Sym M) (f : Sym) (k : CtorSig) : Prop :=
  iteSort? (c.symName f) = none ∧
  ∀ {w : GroundTerm}, c.sortOf w = some k.result → ∀ {bs : List M},
    bs.length = (k.args.map c.sortName).length →
    (∀ (i : Nat) x s, bs[i]? = some x → (k.args.map c.sortName)[i]? = some s → InS I s x) →
    SymE I (c.symName f) bs (elemOf c I w) → ∃ ws, c.sortsOf ws = some k.args ∧ bs = ws.map (elemOf c I)

section Witnessed
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c)
  [OvlOK c] (hg : genWf c = true)
  (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
  (hnm : NamesPlain c) {vars : List Srt} {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M}
  (hvs : vs.length = vars.length)
  (hin : ∀ i < vars.length, InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (keyAt vs i))))
  {L : List CtorSig} (hL : HeadsOK c L) {H : Sym → Bool}
  (hback : ∀ f k, c.isCtor f = false → H f = true → lookupSig (c.rhsCtx L).heads f = some k → HeldBack c I f k)
include hI hg htr hnm hvs hin hL hback

mutual
  /-- **A right-hand side's held variables, at a value** (over a set H of symbols). If the
  element of a value of a well-sorted right-hand side's sort lies in its translation, at a valuation
  of its variables in their sorts, the valuation gives each variable the term holds under
  constructors, injections and the symbols of H the element of a value of its sort. -/
  theorem occsUnder_witnessed : ∀ {t : Term} {s : Srt} {w : GroundTerm},
      sortOfTerm (c.rhsCtx L) vars t = some s → c.sortOf w = some s →
      (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret I e (elemOf c I w) →
      ∀ i ∈ occsUnder c H t, Witnessed c I tbl vs vars e i
    | .var i, s, w, ht, hw, hm => by
      rw [tr_var] at hm
      intro j hj
      rw [occsUnder] at hj
      rw [mem_one hj]
      exact witnessed_of (sortOfTerm_var.mp ht) hw hm
    | .dv _ _, _, _, _, _, _ => fun j hj => by rw [occsUnder] at hj; cases hj
    | .app f ts, s, w, ht, hw, hm => by
      intro j hj
      rw [occsUnder] at hj
      split at hj
      rotate_left
      · cases hj
      rename_i hch
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      cases hc : c.isCtor f with
      | true =>
        obtain ⟨k0, hk0⟩ := Option.isSome_iff_exists.mp hc
        have hkk : k = k0 := by
          simp only [Semantics.rhsCtx, List.append_assoc] at hk'
          rw [lookupSig_append_of_some hk0] at hk'
          exact (Option.some.inj hk').symm
        subst hkk
        rw [kore_app_plain hnm hk0, trArgs_appList, interp_appList] at hm
        obtain ⟨a, ha, bs, hbs, hm⟩ := hm
        have hsorts := rhsSorts hI hg htr hnm hvs hin hL hargs hbs
        obtain ⟨ws, rfl, hws, rfl⟩ := ctor_back hI hg htr hk0 hw hsorts.1 hsorts.2 ⟨a, by
          show (KoreAML.sym (.symbol (c.symName k.name))).interpret I KoreAML.val0 a
          rw [(lookupSig_spec hk0).2]; exact ((Closed.sym _).interp e KoreAML.val0 a).mp ha, hm⟩
        exact occsUnderList_witnessed hargs hws hbs j hj
      | false =>
        have hH : H f = true := by rw [hc] at hch; simpa using hch
        obtain ⟨hit, hb⟩ := hback f k hc hH hk'
        rw [kore_app, tr_symApp, symHead_none hit, trArgs_appList, interp_appList] at hm
        obtain ⟨a, ha, bs, hbs, hm⟩ := hm
        have hsorts := rhsSorts hI hg htr hnm hvs hin hL hargs hbs
        obtain ⟨ws, hws, rfl⟩ := hb hw hsorts.1 hsorts.2 ⟨a, ha, hm⟩
        exact occsUnderList_witnessed hargs hws hbs j hj
    | .inj a b t, s, w, ht, hw, hm => by
      obtain ⟨hab, ht', rfl⟩ := sortOfTerm_inj.mp ht
      rw [Term.kore, KoreAML.tr_injP, interp_injApp] at hm
      obtain ⟨x, hx, hm⟩ := hm
      have hxs := rhsSort hI hg htr hnm hvs hin hL ht' x hx
      obtain ⟨w', hw', rfl, rfl⟩ := inj_back hI hg htr w hab hw hxs hm
      intro j hj
      rw [occsUnder] at hj
      exact occsUnder_witnessed ht' hw' hx j hj
    | .as _ _, _, _, ht, _, _ => absurd ht Model.sortOfTerm_rhs_as
  theorem occsUnderList_witnessed : ∀ {ts : List Term} {ss : List Srt} {ws : List GroundTerm},
      sortsOfTerms (c.rhsCtx L) vars ts = some ss → c.sortsOf ws = some ss →
      All2 (fun φ b => φ.interpret I e b) ((Term.koreList c vs ts).map (KoreAML.tr ⟨tbl, []⟩)) (ws.map (elemOf c I)) →
      ∀ i ∈ occsUnderList c H ts, Witnessed c I tbl vs vars e i
    | [], _, _, _, _, _ => fun j hj => by rw [occsUnderList] at hj; cases hj
    | t :: ts, ss, ws, ht, hws, hbs => by
      obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOfTerms_cons.mp ht
      cases ws with
      | nil => rw [sortsOf_nil] at hws; cases hws
      | cons w ws =>
        obtain ⟨s0, ss0, hw, hws', he⟩ := sortsOf_cons.mp hws
        cases he
        rw [Term.koreList, List.map_cons, List.map_cons] at hbs
        cases hbs with
        | cons hb hbs =>
          intro j hj
          rw [occsUnderList] at hj
          rcases List.mem_append.mp hj with hj | hj
          · exact occsUnder_witnessed h1 hw hb j hj
          · exact occsUnderList_witnessed h2 hws' hbs j hj
end

end Witnessed

/-! ## The symbols with `HeldBack` -/

section Kinds
variable {c : Semantics}

/-- A `collHeld` symbol is no overloading symbol. -/
theorem collHeld_not_ovl {f : Sym} (hh : collHeld c f = true) : c.isOvl f = false := by
  cases ho : c.isOvl f with
  | false => rfl
  | true =>
    obtain ⟨-, hhk, hp, -, -⟩ := c.isOvl_parts ho
    unfold collHeld at hh
    rcases Bool.or_eq_true_iff.mp hh with h | h
    · rw [isHook_patHook h] at hhk; cases hhk
    · unfold Semantics.isCollPat at h
      rw [hhk, if_neg Bool.false_ne_true] at h
      unfold Semantics.isParam at hp
      cases hk : c.lookupParam f with
      | none => rw [hk] at h; simp at h
      | some k => rw [hk] at hp; cases hp

/-- **The signature of a held symbol**: the right side's context gives a `collHeld` symbol that is
no constructor, the signature a left side's context gives it. -/
theorem held_lookup {L : List CtorSig} {f : Sym} {k : CtorSig} (hc : c.isCtor f = false) (hh : collHeld c f = true)
    (hk : lookupSig (c.rhsCtx L).heads f = some k) : lookupSig c.patCtxAll.heads f = some k := by
  have hnc : lookupSig c.ctorSigs f = none :=
    Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hc)
  simp only [Semantics.rhsCtx, List.append_assoc] at hk
  rw [lookupSig_append_of_none hnc] at hk
  simp only [Semantics.patCtxAll, Semantics.patCtx, Semantics.collPatSigs]
  cases hhk : isHook f with
  | true =>
    obtain ⟨k0, hk0⟩ := lookupSig_hookSigs_of_isHook hhk
    rw [lookupSig_append_of_some hk0] at hk
    cases hk
    cases hp : patternHooks.contains f with
    | true =>
      have h1 : lookupSig (hookSigs.filter (patternHooks.contains ·.name)) f = some k := by
        rw [lookupSig_eq, find?_filter_name (patternHooks.contains ·) f hookSigs, hp, if_pos rfl, ← lookupSig_eq, hk0]
      exact lookupSig_append_of_some ((lookupSig_append_of_none hnc).trans h1)
    | false =>
      have hcp : c.isCollPat f = true := by
        unfold collHeld at hh; rw [hp] at hh; simpa using hh
      unfold Semantics.isCollPat at hcp
      rw [hhk, if_pos rfl] at hcp
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcp
      have h1 : lookupSig (hookSigs.filter (patternHooks.contains ·.name)) f = none := by
        rw [lookupSig_eq, find?_filter_name (patternHooks.contains ·) f hookSigs, hp]; rfl
      have h2 : lookupSig (hookSigs.filter (collPatternHooks.contains ·.name)) f = some k := by
        rw [lookupSig_eq, find?_filter_name (collPatternHooks.contains ·) f hookSigs, hcp.2, if_pos rfl,
          ← lookupSig_eq, hk0]
      rw [lookupSig_append_of_none ((lookupSig_append_of_none hnc).trans h1)]
      exact lookupSig_append_of_some (lookupSig_append_of_some h2)
  | false =>
    have hnh := lookupSig_hookSigs_of_not_isHook hhk
    have hp : patternHooks.contains f = false := by
      cases h : patternHooks.contains f with
      | false => rfl
      | true => rw [isHook_patHook h] at hhk; cases hhk
    have hcp : c.isCollPat f = true := by
      unfold collHeld at hh; rw [hp] at hh; simpa using hh
    unfold Semantics.isCollPat at hcp
    rw [hhk, if_neg Bool.false_ne_true] at hcp
    simp only [Bool.and_eq_true] at hcp
    obtain ⟨-, hcp⟩ := hcp
    rw [lookupSig_append_of_none hnh] at hk
    have hnf : ∀ q : Sym → Bool, lookupSig (hookSigs.filter (fun k => q k.name)) f = none := fun q => by
      rw [lookupSig_eq, find?_filter_name q f hookSigs]
      split
      · rw [← lookupSig_eq, hnh]
      · rfl
    cases hkp : c.lookupParam f with
    | none => rw [hkp] at hcp; cases hcp
    | some kp =>
      rw [hkp] at hcp
      simp only at hcp
      rw [lookupSig_append_of_some (by rw [c.lookupSig_params, hkp]; rfl)] at hk
      cases hk
      have hfind := hkp
      rw [Semantics.lookupParam_eq] at hfind
      rw [lookupSig_append_of_none ((lookupSig_append_of_none hnc).trans (hnf _)), List.append_assoc,
        lookupSig_append_of_none (hnf _), lookupSig_eq, List.find?_append, List.find?_map]
      simp only [Function.comp_def]
      rw [find?_filter_of (p := fun x : ParamSig => x.sig.name == f) hfind]
      · rfl
      · cases hi : kp.impl with
        | none => rw [hi] at hcp; simp at hcp
        | some g => rw [hi] at hcp; simpa [hi] using hcp

variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c) [OvlOK c]
  (hg : genWf c = true)
  (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
include hI hg htr

/-- **A collection's symbol has `HeldBack`**: a unit, element or concatenation symbol of a map, list or set collection, by
`head_back`. -/
theorem collHeld_back (hph : patHooksApart c = true) (hcs : collsOK c = true) (hcso : collSortsOK c = true)
    {L : List CtorSig} {f : Sym} {k : CtorSig} (hc : c.isCtor f = false) (hh : collHeld c f = true)
    (hk : lookupSig (c.rhsCtx L).heads f = some k) : HeldBack c I f k := by
  have hov := collHeld_not_ovl hh
  have hd : downHead c f = true := by
    unfold downHead; unfold collHeld at hh; rw [hh]; rfl
  have hR := head_reading hI hph hcs hcso hc hov hd (held_lookup hc hh hk)
  refine ⟨hR.ite, fun {w} hw {bs} hbl hbs hm => ?_⟩
  obtain ⟨ws, hws, hb, -⟩ := head_back hI hg htr hR hw hbl hbs hm
  exact ⟨ws, hws, hb⟩

/-- **An overloading symbol with no function among its overloads has `HeldBack`**: by `ovl_back`,
with no hypothesis on the sorts. -/
theorem ovl_backR (hsc : SortCtx c) {L : List CtorSig} (hL : HeadsOK c L) {f : Sym} {k : CtorSig}
    (ho : c.isOvl f = true) (hnf : OvlLaws.NoFnOver c f)
    (hk : lookupSig (c.rhsCtx L).heads f = some k) : HeldBack c I f k := by
  obtain ⟨o, hlo, rfl⟩ := rhs_lookup_ovl hsc hL hk ho
  obtain ⟨hom, hn, -, hit, -⟩ := OvlLaws.ovl_parts (OvlOK.ok (c := c)) hlo
  have H := (inferInstance : OvlOK c).hyp htr
  obtain ⟨-, -, -, -, hks, -⟩ := OvlLaws.ovl_facts_ovlF H.fnFacts hlo
  refine ⟨hit, fun {w} hw {bs} hbl hbs hm => ?_⟩
  obtain ⟨a, ha, hm⟩ := hm
  obtain ⟨ws, hws, hb, -⟩ := ovl_back hI htr hg _ o.sig hks (OvlLaws.ovlRank_le _)
    (by rw [hn]; exact hnf) hw hbl hbs ⟨a, by rw [← hn] at ha; exact ha, hm⟩
  exact ⟨ws, hws, hb⟩

end Kinds

/-! ## `\in` at a variable -/

section MemElem
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **`\in` at a variable, in a model**: where `V ∈ t` holds at some element, the valuation's
element at V is in t's translation. No evaluation is read: the valuation need not be at values. -/
theorem mem_elem (hI : I ⊧ᴵP Γ c) [OvlOK c] {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M}
    {s S : Srt} {v : Nat} {t : Term} {a : M}
    (hs : s < nRegSorts + c.sortNames.length) (hS : S < nRegSorts + c.sortNames.length)
    (hv : InS I (c.sortName s) (e.evalEvar (tbl.ev (keyAt vs v))))
    (hm : (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c vs (srtOf c S) (.mem s (.var v) t))).interpret I e a) :
    (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret I e (e.evalEvar (tbl.ev (keyAt vs v))) := by
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨σs, hσs1, hσs2⟩ := sortSing hI hs
  obtain ⟨σS, hσS1, hσS2⟩ := sortSing hI hS
  rw [Cond.kore, KoreAML.tr] at hm
  unfold srtOf at hm
  rw [KoreAML.interp_sIn hD hc (S := KoreAML.trSort tbl (KoreAML.srt (c.sortName s)))
    (S' := KoreAML.trSort tbl (KoreAML.srt (c.sortName S)))
    (by rw [trSort_srt]; exact hσs1) (by rw [trSort_srt]; exact hσS1) hσs2 hσS2 (fun b hb => ?_) a] at hm
  · obtain ⟨⟨b, hb, hbt⟩, -⟩ := hm
    have hbe : b = e.evalEvar (tbl.ev (keyAt vs v)) := (tr_var v b).mp hb
    rw [← hbe]; exact hbt
  · have hbe : b = e.evalEvar (tbl.ev (keyAt vs v)) := (tr_var v b).mp hb
    rw [hbe]
    exact (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσs1).mp hv

end MemElem

end KCore
