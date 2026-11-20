/-
  KCore. A unary function's own items in the value model with it read as a set of values.

  In `stdIOver c T n S` (the value model at `T` with the head of the name `n` applied to a value `w`
  giving the elements `S w`), where `n` is the name the theory writes for the function `fn` (its
  symbol's name read as no instance) and no constant:
  - `over_iff_of_good`: a pattern whose symbols are not named `n` and whose applications are rooted
    (`GenEqs.Walk.good`) denotes what it denotes in the value model; `inh_over`, `isSort_over`:
    the inhabitants of a sort element and the sort elements are the value model's, since the
    symbol `inh` holds of no head of a name; `sat_ceilDef_over`.
  - `call_over`: `fn(X0)` denotes `S w` at a valuation sending X0 to the value `w`.
  - `AtT.sat_eqnRight_over`: an equation of `fn` with any right side holds where, at every valuation
    of its guards under which its premise holds, the right side denotes in the value model, among
    the elements of the result sort, the elements `S w` at the argument `w`. The premise and the
    right side apply no symbol named `n`.
  - `AtT.sat_arity_over`: `fn`'s arity item holds where every element of `S w`, `w` of the
    argument sort, is a value of the result sort.
-/
import KcoreSpec.ModelFnOverNames
import KcoreSpec.ClauseExModel

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics} {T : GroundTerm → GroundTerm → Prop}

/-- **A good pattern at the names other than `n` denotes in `stdIOver` what it denotes in the value
model.** -/
theorem over_iff_of_good {n : String} {S : GroundTerm → Set Elem} {φ : KoreAML.P}
    (hg : GenEqs.Walk.good (fun m => m != n) φ = true) (ρ : Valuation Elem) (m : Elem) :
    φ.interpret (stdIOver c T n S) ρ m ↔ φ.interpret (stdI_T c T) ρ m := by
  rw [interpret_over (GenEqs.Walk.good_rooted hg) (fun hn => by
    have := GenEqs.Walk.good_syms hg _ hn
    simp at this) ρ]

/-- The inhabitants of an element in `stdIOver` are its inhabitants in the value model: `inh` holds
of no head of a name. -/
theorem inh_over {n : String} {S : GroundTerm → Set Elem} (σ m : Elem) :
    KoreAML.Inh (stdIOver c T n S) σ m ↔ KoreAML.Inh (stdI_T c T) σ m := by
  have hno : ∀ i, (stdI_T c T).evalSymb .inh i → ¬ GenEqs.headsOf (· = n) i := fun i hi hP => by
    obtain ⟨n', -, he⟩ := (GenEqs.spare_stdI c T (· = n)).sym_e _ _ hP hi
    cases he
  constructor
  · rintro ⟨i, hi, happ⟩
    refine ⟨i, hi, ?_⟩
    rcases happ with ⟨hP, -⟩ | ⟨-, h⟩
    · exact absurd hP (hno i hi)
    · exact h
  · rintro ⟨i, hi, happ⟩
    exact ⟨i, hi, .inr ⟨hno i hi, happ⟩⟩

/-- The sort elements of `stdIOver` are the value model's. -/
theorem isSort_over {n : String} {S : GroundTerm → Set Elem} (σ : Elem) :
    KoreAML.IsSort (stdIOver c T n S) σ ↔ KoreAML.IsSort (stdI_T c T) σ := by
  unfold KoreAML.IsSort
  constructor
  · rintro ⟨s0, hs, hi⟩; exact ⟨s0, hs, (inh_over s0 σ).mp hi⟩
  · rintro ⟨s0, hs, hi⟩; exact ⟨s0, hs, (inh_over s0 σ).mpr hi⟩

/-- `stdIOver` satisfies `⌈_⌉`'s definedness item. -/
theorem sat_ceilDef_over {n : String} {S : GroundTerm → Set Elem} :
    stdIOver c T n S ⊧ᴵ KoreAML.ceilDefItem.pat := by
  have hg : GenEqs.Walk.good (fun m => m != n) KoreAML.ceilDefItem.pat = true := by
    simp only [KoreAML.ceilDefItem]
    refine GenEqs.Walk.good_guarded _ _ (fun g hg => ?_) ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;>
        simp [KoreAML.sortGuard, KoreAML.sortsDomain, GenEqs.Walk.good_member, GenEqs.Walk.good_inhOf,
          GenEqs.Walk.good_included, KoreAML.sym]
    · simp [GenEqs.Walk.good_eq, GenEqs.Walk.good_sCeil, GenEqs.Walk.good_inhOf]
  intro ρ m
  exact (over_iff_of_good hg ρ m).mpr (AtT.sat_ceilDef ρ m)

/-- **The call `fn(X0)` in `stdIOver`**, for a function whose symbol's name is read as no instance and
is no constant, at a valuation sending X0 to the value `w`: the elements `S w`. -/
theorem call_over {f : Sym} (hplain : instDecode? (c.symName f) = none)
    (hsym : GenEqs.spareSymB c (c.symName f) = true) {S : GroundTerm → Set Elem} {tbl : KoreAML.VarTable}
    {e : Valuation Elem} {s : String} {w : GroundTerm}
    (hX : e.evalEvar (tbl.ev (.evar "X0" (KoreAML.srt s))) = .val w) (b : Elem) :
    (KoreAML.tr ⟨tbl, []⟩ (symApp c f (KoreAML.vars (KoreAML.numbered "X" 0 [s])))).interpret
      (stdIOver c T (c.symName f) S) e b ↔ S w b := by
  have hhead : symHead c f = symP (c.symName f) := by unfold symHead; rw [hplain]; rfl
  rw [tr_symApp, hhead, trArgs_appList]
  simp only [KoreAML.vars, KoreAML.numbered, List.map_cons, List.map_nil, Function.comp]
  show (symP (c.symName f) ⬝ KoreAML.tr ⟨tbl, []⟩ (.var (.evar (KoreAML.evar ("X" ++ toString 0) (KoreAML.srt s))))).interpret
    (stdIOver c T (c.symName f) S) e b ↔ S w b
  rw [over_call hsym (by rw [KoreAML.tr]; rfl) (by rw [KoreAML.tr]; simp [AvoidsFn, psyms])]
  rw [KoreAML.tr]
  simp only [KoreAML.interp_evar]
  constructor
  · rintro ⟨w', hw', hS⟩
    have : w' = w := by
      have h2 : Elem.val w' = .val w := hw'.trans hX
      cases h2; rfl
    subst this; exact hS
  · intro hS
    exact ⟨w, hX.symm, hS⟩

namespace AtT

/-- **An equation of a unary function with any right side holds in `stdIOver`**, with the function's
symbol name `n` read as no instance and no constant, where its premise and right side apply no
symbol named `n` (`kok`) and, at every valuation of its guards under which its premise holds, the
right side denotes in the value model, among the elements of the result sort, the elements `S w`
at the argument `w`. `sat_eqnRightEx` with the function read as `S`. -/
theorem sat_eqnRight_over (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {a : Srt}
    (hargs : fn.args = [a]) (hplain : instDecode? (c.symName fn.label) = none)
    (hsym : GenEqs.spareSymB c (c.symName fn.label) = true) {S : GroundTerm → Set Elem}
    {vars : List Srt} {free : Nat → Prop}
    (hnum : ∀ i < vars.length, free i → vars.getD i 0 < nRegSorts + c.sortNames.length)
    {prem right : Kore.Pattern}
    (hkp : GenEqs.Walk.kok (fun m => m != c.symName fn.label) prem = true)
    (hkr : GenEqs.Walk.kok (fun m => m != c.symName fn.label) right = true)
    (hV : ∀ i < vars.length, free i →
      canonKey c vars i ∈ KoreAML.freeOf [] (.implies KoreAML.R prem (eqConclEx c fn right)))
    (hread : ∀ (tbl : KoreAML.VarTable) (e : Valuation Elem) (ws : List GroundTerm) (x : Elem),
      KoreAML.VarKey.sortVar "R" ∈ tbl →
      (∀ k ∈ KoreAML.varsOf (.implies KoreAML.R prem (eqConclEx c fn right)), k ∈ tbl) →
      KoreAML.IsSort (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))) → ArgsAt c tbl e fn.args ws →
      (∀ i < vars.length, free i → InSort c (vars.getD i 0) (e.evalEvar (tbl.ev (canonKey c vars i)))) →
      KoreAML.Inh (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))) x →
      (KoreAML.tr ⟨tbl, []⟩ prem).interpret (stdI_T c T) e x →
      ∀ b, InSort c fn.result b →
        ((KoreAML.tr ⟨tbl, []⟩ right).interpret (stdI_T c T) e b ↔ ∃ w, ws = [w] ∧ S w b)) :
    stdIOver c T (c.symName fn.label) S ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", (⟨[KoreAML.Rv],
      .implies KoreAML.R prem (eqConclEx c fn right), []⟩ : Kore.Axiom)⟩).pat := by
  have hn := h.namesK
  have hfs := h.fnSorts hfn
  have hD := over_defOK (c := c) (T := T) (c.symName fn.label) S
  intro e m
  unfold KoreAML.trAxiom
  dsimp only
  have hsortP : KoreAML.sortOf [] (.implies KoreAML.R prem (eqConclEx c fn right)) =
      some KoreAML.R := rfl
  simp only [hsortP]
  rw [interpret_impl]
  intro hgs
  rw [over_iff_of_good (GenEqs.Walk.good_conjList _ (fun g hg => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hg
    exact GenEqs.Walk.good_guardOf _ _))] at hgs
  generalize hP : (Kore.Pattern.implies KoreAML.R prem (eqConclEx c fn right)) = P at hgs ⊢
  generalize htb : KoreAML.tableOf [KoreAML.Rv] P = tbl at hgs ⊢
  have hvarsP : ∀ k ∈ KoreAML.varsOf P, k ∈ tbl := fun k hk => by
    rw [← htb]; exact List.mem_eraseDups.mpr (List.mem_append_right _ hk)
  have hguard : ∀ k ∈ (([KoreAML.Rv].map KoreAML.sortVarKey) ++ KoreAML.freeOf [] P).eraseDups,
      (KoreAML.guardOf tbl k).interpret (stdI_T c T) e m := fun k hk =>
    conjList_elim hgs _ (List.mem_map.mpr ⟨k, hk, rfl⟩)
  have hfreeP : ∀ k ∈ KoreAML.freeOf [] P, k ∈ (([KoreAML.Rv].map KoreAML.sortVarKey) ++ KoreAML.freeOf [] P).eraseDups :=
    fun k hk => List.mem_eraseDups.mpr (List.mem_append_right _ hk)
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by
    rw [← htb]; exact List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_map.mpr ⟨KoreAML.Rv, List.mem_singleton_self _, rfl⟩))
  have hRs : KoreAML.IsSort (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))) := by
    have := hguard (.sortVar "R") (List.mem_eraseDups.mpr (List.mem_append_left _
      (List.mem_map.mpr ⟨KoreAML.Rv, List.mem_singleton_self _, rfl⟩)))
    obtain ⟨s, hs, he⟩ := sortGuard_iff.mp this
    rw [he]; exact (isSort_iff _).mpr ⟨s, hs, rfl⟩
  have hcallF : ∀ j s, (fn.args.map c.sortName)[j]? = some s →
      KoreAML.VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ KoreAML.freeOf [] P := fun j s hj => by
    rw [← hP, KoreAML.freeOf]
    refine List.mem_append_right _ ?_
    unfold eqConclEx
    rw [KoreAML.freeOf]
    refine List.mem_append_left _ ?_
    rw [freeOf_symApp]
    have := X_mem_call _ 0 j s hj
    rwa [Nat.zero_add] at this
  obtain ⟨ws, hws⟩ := argsAt_of (tbl := tbl) (e := e) (fun s hs => hfs s (List.mem_cons_of_mem _ hs)) (fun j hj => by
    have hs : (fn.args.map c.sortName)[j]? = some (c.sortName (fn.args[j]'hj)) := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
    have hg := hguard _ (hfreeP _ (hcallF j _ hs))
    rw [KoreAML.interp_guard_evar defOK_std, trSort_srt] at hg
    exact (inhOf_sort hn (hfs _ (List.mem_cons_of_mem _ (List.getElem_mem hj))) e _).mp hg)
  have hvin : ∀ i < vars.length, free i →
      InSort c (vars.getD i 0) (e.evalEvar (tbl.ev (canonKey c vars i))) := by
    intro i hi hfi
    have hk : canonKey c vars i ∈ KoreAML.freeOf [] P := hP ▸ hV i hi hfi
    have hg := hguard _ (hfreeP _ hk)
    have hkk := canonKey_eq c hi
    rw [hkk, KoreAML.interp_guard_evar defOK_std, trSort_srt, ← hkk] at hg
    exact (inhOf_sort hn (hnum i hi hfi) e _).mp hg
  have hres := hfs fn.result (List.mem_cons_self ..)
  -- the one argument
  have hwl : ws.length = 1 := by rw [sortsOf_len hws.sorts, hargs]; rfl
  obtain ⟨w, rfl⟩ : ∃ w, ws = [w] := by
    match ws, hwl with
    | [w], _ => exact ⟨w, rfl⟩
  have hX0 : e.evalEvar (tbl.ev (.evar "X0" (KoreAML.srt (c.sortName a)))) = .val w :=
    hws.X 0 w (c.sortName a) rfl (by rw [hargs]; rfl)
  rw [KoreAML.interp_equal hD]
  intro x
  have hPtr : KoreAML.tr ⟨tbl, []⟩ P = KoreAML.sImp (KoreAML.trSort tbl KoreAML.R) (KoreAML.tr ⟨tbl, []⟩ prem)
      (KoreAML.tr ⟨tbl, []⟩ (eqConclEx c fn right)) := by
    rw [← hP, KoreAML.tr]
  have hgR : GenEqs.Walk.good (fun m => m != c.symName fn.label) (KoreAML.inhOf (KoreAML.trSort tbl KoreAML.R)) = true := by
    rw [GenEqs.Walk.good_inhOf]; exact GenEqs.Walk.good_trSort _ _
  rw [hPtr, KoreAML.interp_sImp, over_iff_of_good hgR, over_iff_of_good (GenEqs.Walk.good_tr _ _ hkp)]
  constructor
  · exact fun h' => h'.1
  · intro ha
    refine ⟨ha, fun hprem => ?_⟩
    rw [KoreAML.interp_inhOf_of (R_read e)] at ha
    have hSres : ∀ b, (KoreAML.trSort tbl (KoreAML.srt (c.sortName fn.result))).interpret
        (stdIOver c T (c.symName fn.label) S) e b ↔ b = .srt fn.result := fun b => by
      rw [over_iff_of_good (GenEqs.Walk.good_trSort _ _), trSort_srt]; exact sort_den hn hres e b
    have hRo : ∀ b, (KoreAML.trSort tbl KoreAML.R).interpret (stdIOver c T (c.symName fn.label) S) e b ↔
        b = e.evalEvar (tbl.ev (.sortVar "R")) := fun b => by
      rw [over_iff_of_good (GenEqs.Walk.good_trSort _ _)]; exact R_read e b
    unfold eqConclEx
    rw [KoreAML.tr, KoreAML.interp_sEquals hD sat_ceilDef_over hSres hRo
      ((isSort_over _).mpr ((isSort_iff _).mpr ⟨fn.result, List.mem_range.mpr hres, rfl⟩)) ((isSort_over _).mpr hRs)]
    refine ⟨(inh_over _ _).mpr ha, fun b hb => ?_⟩
    rw [inh_over, inh_srt] at hb
    rw [hargs, List.map_cons, List.map_nil]
    rw [call_over hplain hsym hX0, over_iff_of_good (GenEqs.Walk.good_tr _ _ hkr)]
    rw [hread tbl e [w] x hRmem (fun k hk => hvarsP k (hP ▸ hk)) hRs hws hvin ha hprem b hb]
    constructor
    · intro hS; exact ⟨w, rfl, hS⟩
    · rintro ⟨w', hw', hS⟩
      cases hw'; exact hS

/-- **The arity item of a unary function holds in `stdIOver`**, with its symbol name read as no
instance and no constant, where every element of `S w`, at a value `w` of the argument sort, is a
value of the result sort. -/
theorem sat_arity_over (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {a : Srt}
    (hargs : fn.args = [a]) (hplain : instDecode? (c.symName fn.label) = none)
    (hsym : GenEqs.spareSymB c (c.symName fn.label) = true) {S : GroundTerm → Set Elem}
    (hS : ∀ w x, c.sortOf w = some a → S w x → InSort c fn.result x) :
    stdIOver c T (c.symName fn.label) S ⊧ᴵ (symArityItem c fn.sig).pat := by
  have hn := h.namesK
  have hfs := h.fnSorts hfn
  have hres := hfs fn.result (List.mem_cons_self ..)
  have ha : a < nRegSorts + c.sortNames.length := hfs a (List.mem_cons_of_mem _ (by rw [hargs]; exact List.mem_singleton_self _))
  have hD := over_defOK (c := c) (T := T) (c.symName fn.label) S
  have hw : ∀ ps, symApp c fn.sig.name ps = .app ⟨⟨c.symName fn.label⟩⟩ (([] : List String).map KoreAML.srt) ps := by
    intro ps; show symApp c fn.label ps = _; unfold symApp; rw [hplain]; rfl
  intro e m
  rw [symArityItem_of_symApp hw]
  have hsa : fn.sig.args = [a] := hargs
  rw [hsa]
  show (symP (c.symName fn.label) ⬝ KoreAML.inhOf (sortP (c.sortName a)) ⊆⊆
      KoreAML.inhOf (sortP (c.sortName fn.sig.result))).interpret (stdIOver c T (c.symName fn.label) S) e m
  rw [KoreAML.interp_included hD]
  intro x hx
  have hgi : ∀ s, GenEqs.Walk.good (fun m => m != c.symName fn.label) (KoreAML.inhOf (sortP s)) = true := fun s => by
    rw [GenEqs.Walk.good_inhOf]; rfl
  rw [over_iff_of_good (hgi _)]
  refine (inhOf_sort hn hres e x).mpr ?_
  rw [over_call hsym (GenEqs.Walk.good_rooted (hgi _)) (fun hm => by
    have := GenEqs.Walk.good_syms (hgi (c.sortName a)) _ hm
    simp at this)] at hx
  obtain ⟨w, hw, hSw⟩ := hx
  exact hS w x ((inhOf_sort hn ha e _).mp hw) hSw

end AtT

end Model

end Faithful

end KCore
