/-
  KCore. A right-hand side read downwards in a model of `Γ c`, at a valuation of its variables in
  their sorts (elements, not necessarily values').

  - The elements of a well-sorted right-hand side's translation lie in its sort (`rhsSort`): each
    head the right-hand side's context lists is a kernel symbol, whose arity item (`symArityItem`,
    `ΓSig`) puts what it builds from elements of its argument sorts in its result sort, the head
    `Lblite` of an `ite{X}` symbol included; an injection by Cons-Fun.
  - If the element of a value lies in the translation, the valuation gives each variable the term
    holds under constructors and injections only (`ctorOccs`) the element of a value of its sort
    (`ctorOccs_witnessed`): a constructor's image at a value is that constructor applied to values
    whose elements its arguments are (`ctor_back`: Cons-Fun, Cons-Inj, Cons-Dist), an injection's
    image at a value is the injection of a value whose element its argument is (`inj_back`:
    Cons-Coh, Cons-Inj, Cons-Dist, Cons-Dist′ at the listed lower bounds).
-/
import KcoreSpec.FaithfulNeg
import KcoreSpec.ModelPat

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed VarKey VarTable)

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c)

include hI in
/-- G-arity of a kernel symbol, at the head `Term.kore` applies (`symHead`) and elements of its
argument sorts: what it builds lies in its result sort. -/
theorem head_arity {k : CtorSig} (hk : k ∈ kernelSyms c) {e : Valuation M} {a : M}
    (ha : (symHead c k.name).interpret I e a) {bs : List M}
    (hbl : bs.length = (k.args.map c.sortName).length)
    (hbs : ∀ (i : Nat) x s, bs[i]? = some x → (k.args.map c.sortName)[i]? = some s → InS I s x) {m : M}
    (hm : AppE I a bs m) : InS I (c.sortName k.result) m := by
  have hD := defOK hI
  have hit := sat_sigItem hI (sig_arity (c := c) hk)
  have hargs : ∀ (ss : List Srt) (bs : List M), bs.length = (ss.map c.sortName).length →
      (∀ (i : Nat) x s, bs[i]? = some x → (ss.map c.sortName)[i]? = some s → InS I s x) →
      All2 (fun φ b => φ.interpret I KoreAML.val0 b)
        (ss.map fun s => KoreAML.inhOf (KoreAML.Cons.sortP (c.sortName s))) bs := by
    intro ss
    induction ss with
    | nil => intro bs hl _; cases bs with
      | nil => exact .nil
      | cons _ _ => simp at hl
    | cons s ss ih =>
      intro bs hl hb
      cases bs with
      | nil => simp at hl
      | cons b bs =>
        exact .cons ((inS_iff _).mpr (hb 0 b (c.sortName s) rfl rfl))
          (ih bs (by simpa using hl) (fun i x s' h1 h2 => hb (i + 1) x s' (by simpa using h1) (by simpa using h2)))
  obtain ⟨h, xs, -, hw⟩ := symApp_head c k.name
  rw [symArityItem_of_symApp hw] at hit
  rw [symHead_of_symApp hw] at ha
  have hinc := (KoreAML.interp_included hD).mp (hit KoreAML.val0 default) m
  apply hinc
  rw [interp_appList]
  exact ⟨a, ((instHeadP_closed h xs).interp e KoreAML.val0 a).mp ha, bs, hargs k.args bs hbl hbs, hm⟩

variable [OvlOK c] (hg : genWf c = true)
  (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
  (hnm : NamesPlain c) {vars : List Srt} {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M}
  (hvs : vs.length = vars.length)
  (hin : ∀ i < vars.length, InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (keyAt vs i))))
  {L : List CtorSig} (hL : HeadsOK c L)
include hI hg htr hnm hvs hin hL

-- the lists' halves of the mutual blocks read the section's hypotheses through the terms' halves
set_option linter.unusedSectionVars false

mutual
  /-- **The sort of a right-hand side, in a model**: the elements of a well-sorted right-hand
  side's translation, at a valuation of its variables in their sorts, lie in its sort. -/
  theorem rhsSort : ∀ {t : Term} {s : Srt}, sortOfTerm (c.rhsCtx L) vars t = some s →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret I e m → InS I (c.sortName s) m
    | .var i, s, ht, m, hm => by
      have hi := sortOfTerm_var.mp ht
      have hlt : i < vars.length := (List.getElem?_eq_some_iff.mp hi).1
      rw [tr_var] at hm
      rw [hm]
      have := hin i hlt
      rwa [List.getD_eq_getElem?_getD, hi, Option.getD_some] at this
    | .dv s' lit, s, ht, m, hm => by
      obtain ⟨hok, rfl⟩ := sortOfTerm_dv.mp ht
      rw [tr_kore_dv hI hg htr hnm hvs hin] at hm
      have hs := elemOf_spec hI (sortOf_dv.mpr ⟨hok, rfl⟩) e
      rw [(hs.1 m).mp hm]
      exact (inS_iff _).mp hs.2
    | .app f ts, s, ht, m, hm => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      obtain ⟨hkm, hkn⟩ := lookupSig_spec hk'
      rw [kore_app, tr_symApp, trArgs_appList, interp_appList] at hm
      obtain ⟨a, ha, bs, hbs, hm⟩ := hm
      have hsorts := rhsSorts hargs hbs
      subst hkn
      exact head_arity hI (Model.rhsHead_kernel hL hkm) ha hsorts.1 hsorts.2 hm
    | .inj a b t, s, ht, m, hm => by
      obtain ⟨hab, ht', rfl⟩ := sortOfTerm_inj.mp ht
      rw [Term.kore, KoreAML.tr_injP, interp_injApp] at hm
      obtain ⟨x, hx, hm⟩ := hm
      have hxs := rhsSort ht' x hx
      obtain ⟨y, hy, hys⟩ := gen_fun hI (genWf_sub hg hab).1 (gensF_inj hab) rfl (xs := [x]) rfl (single_sorts hxs)
      rw [(hys m).mp hm]; exact hy
    | .as _ _, s, ht, _, _ => absurd ht Model.sortOfTerm_rhs_as
  theorem rhsSorts : ∀ {ts : List Term} {ss : List Srt} {bs : List M},
      sortsOfTerms (c.rhsCtx L) vars ts = some ss →
      All2 (fun φ b => φ.interpret I e b) ((Term.koreList c vs ts).map (KoreAML.tr ⟨tbl, []⟩)) bs →
      bs.length = (ss.map c.sortName).length ∧
        ∀ (i : Nat) x s, bs[i]? = some x → (ss.map c.sortName)[i]? = some s → InS I s x
    | [], ss, bs, ht, hbs => by
      rw [sortsOfTerms_nil.mp ht]
      rw [Term.koreList] at hbs
      cases hbs
      exact ⟨rfl, fun i x s h _ => by simp at h⟩
    | t :: ts, ss, bs, ht, hbs => by
      obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOfTerms_cons.mp ht
      rw [Term.koreList, List.map_cons] at hbs
      cases hbs with
      | cons hb hbs =>
        have ih := rhsSorts h2 hbs
        refine ⟨by simp [ih.1], fun i x s' hx hs' => ?_⟩
        cases i with
        | zero =>
          simp at hx hs'; subst hx; subst hs'
          exact rhsSort h1 _ hb
        | succ i => exact ih.2 i x s' (by simpa using hx) (by simpa using hs')
end

mutual
  /-- **A right-hand side's constructor variables, at a value.** If the element of a value of a
  well-sorted right-hand side's sort lies in its translation, at a valuation of its variables in
  their sorts, the valuation gives each variable the term holds under constructors and injections
  only (`ctorOccs`) the element of a value of its sort. -/
  theorem ctorOccs_witnessed : ∀ {t : Term} {s : Srt} {w : GroundTerm},
      sortOfTerm (c.rhsCtx L) vars t = some s → c.sortOf w = some s →
      (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret I e (elemOf c I w) →
      ∀ i ∈ ctorOccs c t, Witnessed c I tbl vs vars e i
    | .var i, s, w, ht, hw, hm => by
      rw [tr_var] at hm
      intro j hj
      rw [ctorOccs] at hj
      rw [mem_one hj]
      exact witnessed_of (sortOfTerm_var.mp ht) hw hm
    | .dv _ _, _, _, _, _, _ => fun j hj => by rw [ctorOccs] at hj; cases hj
    | .app f ts, s, w, ht, hw, hm => by
      intro j hj
      rw [ctorOccs] at hj
      split at hj
      rotate_left
      · cases hj
      rename_i hc
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
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
      exact ctorOccsList_witnessed hargs hws hbs j hj
    | .inj a b t, s, w, ht, hw, hm => by
      obtain ⟨hab, ht', rfl⟩ := sortOfTerm_inj.mp ht
      rw [Term.kore, KoreAML.tr_injP, interp_injApp] at hm
      obtain ⟨x, hx, hm⟩ := hm
      have hxs := rhsSort hI hg htr hnm hvs hin hL ht' x hx
      obtain ⟨w', hw', rfl, rfl⟩ := inj_back hI hg htr w hab hw hxs hm
      intro j hj
      rw [ctorOccs] at hj
      exact ctorOccs_witnessed ht' hw' hx j hj
    | .as _ _, _, _, ht, _, _ => absurd ht Model.sortOfTerm_rhs_as
  theorem ctorOccsList_witnessed : ∀ {ts : List Term} {ss : List Srt} {ws : List GroundTerm},
      sortsOfTerms (c.rhsCtx L) vars ts = some ss → c.sortsOf ws = some ss →
      All2 (fun φ b => φ.interpret I e b) ((Term.koreList c vs ts).map (KoreAML.tr ⟨tbl, []⟩)) (ws.map (elemOf c I)) →
      ∀ i ∈ ctorOccsList c ts, Witnessed c I tbl vs vars e i
    | [], _, _, _, _, _ => fun j hj => by rw [ctorOccsList] at hj; cases hj
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
          rw [ctorOccsList] at hj
          rcases List.mem_append.mp hj with hj | hj
          · exact ctorOccs_witnessed h1 hw hb j hj
          · exact ctorOccsList_witnessed h2 hws' hbs j hj
end

end

end Faithful

end KCore
