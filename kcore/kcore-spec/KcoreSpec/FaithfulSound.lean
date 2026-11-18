/-
  KCore. Step soundness from what the proof reads: `HypSound`.

  The soundness proofs read of a semantics its well-formedness (`sortedOK`, `srReady`), the
  well-formedness of its names and sort numbers (`NamesNumbered`), and decidable facts about its
  values, its collections and its pattern symbols (`genWf`, `patHooksApart`, `collSortsOK`,
  `collsOK`, `patHeadsOK`). They do not read termination, totality, `ClausesAgree` or
  `MatchIndependent`, which `Hyp` assumes: every clause's exclusion is empty where it fails, which
  the downward reading of patterns gives for every pattern a well-formed semantics has.
-/
import KcoreSpec.FaithfulCollPat

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed KGround VarKey VarTable)

/-- **What the soundness proof reads of a semantics**, its well-formedness as `okAll` (of which the
proof reads `sortedOK`, `HypSoundCore`): it is well formed (`okAll`), its function labels are
distinct and its subsorts closed (`srReady`), its names and sort numbers are well
formed (`NamesNumbered`), its values are generated (`genWf`), the map pattern symbols are not
constructors (`patHooksApart`), no collection sort holds a domain value (`collSortsOK`), the
definition's own collections are built by the parameters their names denote (`collsOK`), and
every symbol a left-hand side may apply is one the downward reading covers (`patHeadsOK`), and its
overloading symbols are as the readings take them (`OvlOK`). Each is decidable on the data. -/
def HypSound (c : Semantics) : Prop :=
  c.okAll = true ∧ c.srReady = true ∧ NamesNumbered c ∧ genWf c = true ∧ patHooksApart c = true ∧
    collSortsOK c = true ∧ collsOK c = true ∧ patHeadsOK c = true ∧ OvlOK c

/-- `HypSound` with `sortedOK` in place of `okAll`: what the soundness proof reads of the clauses
and rules is that they are well sorted and bind their variables. -/
def HypSoundCore (c : Semantics) : Prop :=
  c.sortedOK = true ∧ c.srReady = true ∧ NamesNumbered c ∧ genWf c = true ∧ patHooksApart c = true ∧
    collSortsOK c = true ∧ collsOK c = true ∧ patHeadsOK c = true ∧ OvlOK c

theorem HypSound.core {c : Semantics} (h : HypSound c) : HypSoundCore c :=
  ⟨Semantics.sortedOK_of_okAll h.1, h.2⟩

section
variable {c : Semantics} (h : patHeadsOK c = true)
include h

mutual
  /-- A well-sorted pattern of a left-hand side is in the downward reading's scope. -/
  theorem collPat_of_sorted : ∀ {vars : List Srt} {p : Term} {s : Srt},
      sortOfTerm c.patCtxAll vars p = some s → collPat c p = true
    | _, .var _, _, _ => by rw [collPat]
    | _, .dv _ _, _, _ => by rw [collPat]
    | _, .app f ts, _, ht => by
      obtain ⟨k, hk, hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨hkm, hkn⟩ := lookupSig_spec hk
      have hh := List.all_eq_true.mp h k hkm
      rw [hkn] at hh
      rw [collPat, hh, collPats_of_sorted hargs]
      rfl
    | _, .inj _ _ t, _, ht => by
      obtain ⟨-, ht', -⟩ := sortOfTerm_inj.mp ht
      rw [collPat]
      exact collPat_of_sorted ht'
    | _, .as t _, _, ht => by
      obtain ⟨-, ht'⟩ := Exec.sortOfTerm_as ht
      rw [collPat]
      exact collPat_of_sorted ht'
  theorem collPats_of_sorted : ∀ {vars : List Srt} {ps : List Term} {ss : List Srt},
      sortsOfTerms c.patCtxAll vars ps = some ss → collPats c ps = true
    | _, [], _, _ => by rw [collPats]
    | _, p :: ps, _, ht => by
      obtain ⟨s, ss', h1, h2, -⟩ := sortsOfTerms_cons.mp ht
      rw [collPats, collPat_of_sorted h1, collPats_of_sorted h2]
      rfl
end

end

/-- **Step soundness**: every step of `Step` is a theorem of `Γ`, `⟦x⟧ → •⟦y⟧`, for a semantics
that satisfies `HypSoundCore`: in every model of `Γ c`, the configuration `x` has the configuration
`y` as a successor. Every clause's exclusion and every competing rule's `applies` is empty where the
kernel says it fails (`exclusion_emptyC`, `applies_emptyC`): every pattern of a clause or a
left-hand side is in the downward reading's scope (`collPat_of_sorted`), so no clause or rule needs
to be read positively only. -/
theorem step_sound_core (c : Semantics) (hpreTop : c.clausesPreTop = true) (h : HypSoundCore c) (hb : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true) (htop : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top)
    (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) :
    ∀ x y : Config c, Step c x y → Γ c ⊧ (den c x.val ⇒ KoreAML.sNext (den c y.val)) := by
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  intro x y hstep M _ I hI e m hm
  have hex : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ExclEmpty c I fn cl := fun fn hfn cl hcl => by
    obtain ⟨hp', hb', -⟩ := clause_ctx hok hbc hfn hcl
    exact fun hws _ hkeys hXkeys hRkey _ hX _ hR hσR hfail m =>
      exclusion_emptyC hI hph hcs hcso hg hsc.trans hnn.1 (clause_preTop (hpreTop := hpreTop) hok hfn hcl) hp' hb' (collPats_of_sorted hph' hp') hws hkeys hXkeys
        hRkey hX hR hσR hfail m
  refine step_at4 (hpreTop := hpreTop) hI hnn hsc hok hbc hph
    (fun fn hfn cl hcl _ => hex fn hfn cl hcl) hb htop (fun r hr _ => ?_) hstep e m hm
  obtain ⟨hlhs, -⟩ := rule_ctx hok hr
  exact fun hx _ hkeys e hfail =>
    applies_emptyC hI hph hcs hcso hg hsc.trans hnn.1 hlhs (Exec.binds_all (hb _ hr)) (collPat_of_sorted hph' hlhs) (htop _ hr).1 hx hkeys e hfail

/-- **An undefined result is a theorem of `Γ`**, for a semantics that satisfies `HypSoundCore`:
where `f` has the result none at `vs`, `Γ` entails `f(vs) = ⊥` (`eval_den4`, its competitors' exclusions
empty as in `step_sound_core`). -/
theorem eval_none_sound_core (c : Semantics) (hpreTop : c.clausesPreTop = true) (h : HypSoundCore c)
    (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) {f : Sym} {fn : Fn} {vs : List GroundTerm}
    (hE : Eval c f vs none) (hfn : c.lookupFn f = some fn) (hvs : c.sortsOf vs = some fn.args) :
    Γ c ⊧ (KoreAML.den (symApp c f (GroundTerm.koreList c vs)) ≡ ⊥) := by
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  intro M _ I hI e m
  have hex : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ExclEmpty c I fn cl := fun fn hfn cl hcl => by
    obtain ⟨hp', hb', -⟩ := clause_ctx hok hbc hfn hcl
    exact fun hws _ hkeys hXkeys hRkey _ hX _ hR hσR hfail m =>
      exclusion_emptyC hI hph hcs hcso hg hsc.trans hnn.1 (clause_preTop (hpreTop := hpreTop) hok hfn hcl) hp' hb' (collPats_of_sorted hph' hp') hws hkeys hXkeys
        hRkey hX hR hσR hfail m
  rw [KoreAML.interp_equal (defOK hI)]
  intro a
  rw [eval_den4 (hpreTop := hpreTop) hI hnn hsc hok hbc hph (fun fn hfn cl hcl _ => hex fn hfn cl hcl) hE hfn hvs e a]
  exact ⟨fun h => h.elim, fun h => by simp [Pattern.interpret] at h⟩

/-- **Step soundness** under `HypSound`: `step_sound_core`. -/
theorem step_sound (c : Semantics) (h : HypSound c) (hb : ∀ r ∈ c.rules, binds r.vars.length (varOccs r.lhs) = true) (htop : ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top)
    (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) :
    ∀ x y : Config c, Step c x y → Γ c ⊧ (den c x.val ⇒ KoreAML.sNext (den c y.val)) :=
  have hpreTop := Semantics.preTop_of_okAll h.1
  step_sound_core (hpreTop := hpreTop) c h.core hb htop hbc

end Faithful

end KCore
