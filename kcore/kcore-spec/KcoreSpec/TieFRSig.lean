/-
  The readings of KcoreSpec/TieFRRead.lean and the decision of KcoreSpec/TieFRTightB.lean in a
  model of the signature (`ΓSig`), with no fact of the values.

  `readings_of_frT` and `tightSem_of_guardsB` take `HoldsShape.NodeFacts` whole and
  `Faithful.TermsInSort`. Of `NodeFacts` their proofs read three facts of the model: definedness,
  the item of `⌈_⌉`, and that each numbered sort denotes one sort (`SigFacts`). Every model of
  definedness and `ΓSig` has them (`sigFacts_of_sig`: `ceilDefItem` and the sort constants are
  items of `sigItems`). That a value is one element of its sort and that two values are apart
  (`NodeFacts.val`, `NodeFacts.apart`) are not read; no item of `ΓSig` states them.

  `TermsInSort` is not a consequence of `ΓSig`: of an injection `inj{a,b}(t)` it says the elements
  lie in b, and `ΓSig` holds no item for `inj`: the arity items of `sigItems` are those of
  `kernelSyms` (constructors, functions, parameters, hooked symbols, overloads), and an injection
  is none of them (`rhsSort_at` reads Cons-Fun of the injection, an item of `ΓCons`). `rhsSort_sig`
  gives the sort of a term from `ΓSig`, where the term holds no injection (`injFree`) or each
  injection of a subsort pair puts its source sort's elements in its target sort (`InjIn`):
  - a variable lies in its sort by the hypothesis on the valuation;
  - an application lies in its head's result sort by the head's arity item (`symArityItem`, in
    `sigItems`), its arguments in the argument sorts;
  - a literal `\dv{s}(lit)` lies in s by the arity item of `lit` (`dvArityAll`, the second part of
    `ΓSig`, read at the one literal) at the sort s, which is numbered (`hvn`, a fact of the
    definition);
  - an injection `inj{a,b}(t)` lies in b by `InjIn`.
  So `TermsInSortNI` holds in every model of `ΓSig` (`termsInSortNI_of_sig`), and `TermsInSort`
  in every model of `ΓSig` with `InjIn` (`termsInSort_of_sig_inj`).

  `InjIn` is what the text's declaration `symbol inj{From, To}(From) : To` states: its arity item
  (`injArityP`, `injArityP_shape`) at the two sorts of a subsort pair, both numbered
  (`injIn_of_arity`). That item is an item of the text's signature which `ΓSig` leaves out. The
  text's subsort sentence of the pair, `\exists{R}(Val:b, \equals{b,R}(Val, inj{a,b}(From:a)))`,
  does not give it: an equation at the sort b compares its sides among b's elements only
  (`interp_sEquals`), so the sentence says that `inj{a,b}(x)` holds one element among b's, and
  nothing of an element outside b. Cons-Fun of the injection says both; `TermsInSort` reads the
  inclusion alone.

  The lemmas below are those of the two files with `SigFacts` for `NodeFacts` and, for
  `TermsInSort`, `TermsInSortOn ok`: the fact for the terms a decision `ok` accepts, with the
  premise that `ok` accepts each term read (`tightOnB ok` for those read from the text).
  `TermsInSortNI`, `tightNIB` are the instance at `injFree`. At `ok := fun _ => true` the premises
  on the terms hold of every term and pattern (`tightOnB_all`) and `TermsInSortOn` is
  `TermsInSort` (`termsInSortOn_of`), so a text whose terms hold injections takes the lemmas with
  `sig_of_core_all` and no decision on its terms.
-/
import KcoreSpec.TieFRTightB
import KcoreSpec.TieRhs

set_option autoImplicit false

namespace KCore

namespace TieFRSig

open ML KoreAML Faithful
open KCore.TieFRRead KCore.TermRT KCore.TieFRRT KCore.TieFRTightB

/-! ## The facts of the model -/

/-- The facts of a model the readings take: definedness, the item of `⌈_⌉`, and that each numbered
sort denotes one sort. -/
structure SigFacts (c : Semantics) {M : Type} (I : Interpretation KoreAML.Sym M) : Prop where
  defOK : KoreAML.DefOK I
  ceilDef : I ⊧ᴵ KoreAML.ceilDefItem.pat
  sort : ∀ {s : Srt}, s < nRegSorts + c.sortNames.length → ∃ τ, KoreAML.IsSort I τ ∧
    ∀ (tbl : KoreAML.VarTable) (e : Valuation M) (a : M), (KoreAML.trSort tbl (srtOf c s)).interpret I e a ↔ a = τ

/-- `NodeFacts` holds them. -/
theorem sigFacts_of_node {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}
    (F : HoldsShape.NodeFacts c I) : SigFacts c I := ⟨F.defOK, F.ceilDef, F.sort⟩

/-- **A model of definedness and the signature has them.** -/
theorem sigFacts_of_sig {c : Semantics} [OvlOK c] {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hD : DefOK I) (hSig : I ⊧ᴵP ΓSig c) : SigFacts c I := by
  refine ⟨hD, hSig _ (Or.inl (Or.inl ⟨_, sig_ceilDef, rfl⟩)), fun {s} hs => ?_⟩
  obtain ⟨τ, hτ, hτs⟩ := TieRhs.sortSing_sig hD hSig hs
  exact ⟨τ, hτs, fun tbl e a => by unfold srtOf; rw [trSort_srt]; exact hτ a⟩

/-! ## The sort of a term -/

mutual
  /-- The term holds no injection. -/
  def injFree : Term → Bool
    | .var _ => true
    | .app _ ts => injFreeList ts
    | .inj _ _ _ => false
    | .as t _ => injFree t
    | .dv _ _ => true
    termination_by structural t => t
  def injFreeList : List Term → Bool
    | [] => true
    | t :: ts => injFree t && injFreeList ts
    termination_by structural ts => ts
end

/-- `Faithful.TermsInSort` for the terms `ok` accepts. -/
def TermsInSortOn (ok : Term → Bool) (c : Semantics) {M : Type} [Inhabited M] (I : Interpretation KoreAML.Sym M) : Prop :=
  ∀ {vars : List Srt} {tbl : VarTable} {e : Valuation M} {t : Term} {s : Srt}, ok t = true →
    sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t = some s → s < nRegSorts + c.sortNames.length →
    (∀ i ∈ varOccs t, InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (canonKey c vars i)))) →
    ∀ a, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c vars) t)).interpret I e a → InS I (c.sortName s) a

/-- `Faithful.TermsInSort` for the terms that hold no injection. -/
abbrev TermsInSortNI (c : Semantics) {M : Type} [Inhabited M] (I : Interpretation KoreAML.Sym M) : Prop :=
  TermsInSortOn injFree c I

/-- `TermsInSort` gives it, whatever `ok` accepts. -/
theorem termsInSortOn_of {ok : Term → Bool} {c : Semantics} {M : Type} [Inhabited M]
    {I : Interpretation KoreAML.Sym M} (h : TermsInSort c I) : TermsInSortOn ok c I :=
  fun _ ht hs hin a ha => h ht hs hin a ha

/-- `TermsInSort` gives it. -/
theorem termsInSortNI_of {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (h : TermsInSort c I) : TermsInSortNI c I := termsInSortOn_of h

/-- An injection of a subsort pair puts the elements of its source sort in its target sort. -/
def InjIn (c : Semantics) {M : Type} [Inhabited M] (I : Interpretation KoreAML.Sym M) : Prop :=
  ∀ {a b : Srt}, (a, b) ∈ c.subsorts → ∀ {x m : M}, InS I (c.sortName a) x →
    GS I (c.sortName b) (.inj (c.sortName a)) [x] m → InS I (c.sortName b) m

/-- The arity item of the declaration `symbol inj{From, To}(From) : To`: at two sorts, what `inj`
builds of an element of the first lies in the second. -/
def injArityP : P :=
  guarded [sortGuard ⟨1⟩, sortGuard ⟨2⟩]
    (appList (appList (sym (.symbol "inj")) [.evar ⟨1⟩, .evar ⟨2⟩]) [inhOf (.evar ⟨1⟩)] ⊆⊆ inhOf (.evar ⟨2⟩))

/-- It is `arityItem` of that declaration, whatever its attributes. -/
theorem injArityP_shape (hooked : Bool) (attrs : List String) :
    (arityItem ⟨"inj", [⟨⟨⟨"From"⟩⟩⟩, ⟨⟨⟨"To"⟩⟩⟩], [.var ⟨⟨⟨"From"⟩⟩⟩], .var ⟨⟨⟨"To"⟩⟩⟩, hooked, attrs⟩).pat = injArityP := by
  cases hooked <;> rfl

/-- **`InjIn` in a model of definedness, the signature and `inj`'s arity item**, the sorts of each
subsort pair being numbered. `ΓSig` holds no item for `inj`; the text's signature holds this one. -/
theorem injIn_of_arity {c : Semantics} [OvlOK c] {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hD : DefOK I) (hSig : I ⊧ᴵP ΓSig c)
    (hsn : ∀ {a b : Srt}, (a, b) ∈ c.subsorts →
      a < nRegSorts + c.sortNames.length ∧ b < nRegSorts + c.sortNames.length)
    (hA : I ⊧ᴵ injArityP) : InjIn c I := by
  intro a b hab x m hx hm
  obtain ⟨σa, hσa, hσaS⟩ := TieRhs.sortSing_sig hD hSig (hsn hab).1
  obtain ⟨σb, hσb, hσbS⟩ := TieRhs.sortSing_sig hD hSig (hsn hab).2
  obtain ⟨d, hd, happ⟩ := hm
  let e : Valuation M := ⟨fun y => match y with | ⟨1⟩ => σa | _ => σb, fun _ _ => False⟩
  have h1 : (guarded [sortGuard ⟨1⟩, sortGuard ⟨2⟩]
      (appList (appList (sym (.symbol "inj")) [.evar ⟨1⟩, .evar ⟨2⟩]) [inhOf (.evar ⟨1⟩)] ⊆⊆
        inhOf (.evar ⟨2⟩))).interpret I e default := hA e default
  have h2 := interp_guarded h1 (fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · unfold KoreAML.sortGuard; rw [KoreAML.interp_member hD, KoreAML.interp_sortsDomain]; exact hσaS
    · unfold KoreAML.sortGuard; rw [KoreAML.interp_member hD, KoreAML.interp_sortsDomain]; exact hσbS)
  rw [KoreAML.interp_included hD] at h2
  have hd' : (KoreAML.appList (KoreAML.sym (.symbol "inj"))
      [KoreAML.Cons.sortP (c.sortName a), KoreAML.Cons.sortP (c.sortName b)]).interpret I KoreAML.val0 d := hd
  rw [interp_appList] at hd'
  obtain ⟨a0, ha0, bs, hbs, happ0⟩ := hd'
  have hhead : (appList (sym (.symbol "inj")) [.evar ⟨1⟩, .evar ⟨2⟩]).interpret I e d := by
    rw [interp_appList]
    refine ⟨a0, ha0, bs, ?_, happ0⟩
    match bs, hbs with
    | _, .cons hb1 (.cons hb2 .nil) =>
      exact .cons (KoreAML.interp_evar.mpr ((hσa _).mp hb1)) (.cons (KoreAML.interp_evar.mpr ((hσb _).mp hb2)) .nil)
  have hxa : (inhOf (.evar ⟨1⟩ : P)).interpret I e x :=
    (KoreAML.interp_inhOf_of (S := (.evar ⟨1⟩ : P)) (σ := σa) (e := e) (fun _ => KoreAML.interp_evar)).mpr
      ((KoreAML.interp_inhOf_of (S := KoreAML.Cons.sortP (c.sortName a)) (e := KoreAML.val0) (fun a => hσa a)).mp hx)
  have h3 := h2 m (by
    rw [interp_appList]
    exact ⟨d, hhead, [x], .cons hxa .nil, happ⟩)
  rw [KoreAML.interp_inhOf_of (S := (.evar ⟨2⟩ : P)) (σ := σb) (fun _ => KoreAML.interp_evar)] at h3
  exact (KoreAML.interp_inhOf_of (S := KoreAML.Cons.sortP (c.sortName b)) (e := KoreAML.val0) (fun a => hσb a)).mpr h3

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
  (hD : DefOK I) (hSig : I ⊧ᴵP ΓSig c)
include hD hSig

/-- The arity item of a kernel symbol, at the head `Term.kore` applies and elements of its argument
sorts: what it builds lies in its result sort. -/
theorem head_arity_sig {k : CtorSig} (hk : k ∈ kernelSyms c) {e : Valuation M} {a : M}
    (ha : (symHead c k.name).interpret I e a) {bs : List M}
    (hbl : bs.length = (k.args.map c.sortName).length)
    (hbs : ∀ (i : Nat) x s, bs[i]? = some x → (k.args.map c.sortName)[i]? = some s → InS I s x) {m : M}
    (hm : AppE I a bs m) : InS I (c.sortName k.result) m := by
  have hit : I ⊧ᴵ (symArityItem c k).pat := hSig _ (Or.inl (Or.inl ⟨_, sig_arity (c := c) hk, rfl⟩))
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

variable [OvlOK c]
  (hvn : ∀ {s : Srt} {lit : Lit}, dvOK c.lib s lit = true → s < nRegSorts + c.sortNames.length)
  {vars : List Srt} {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M} {L : List CtorSig} (hL : HeadsOK c L)
include hvn hL

set_option linter.unusedSectionVars false

mutual
  /-- **The sort of a term, in a model of the signature**: its elements, at a valuation of its
  variables in their sorts, lie in its sort, where the term holds no injection or each injection
  puts its source sort's elements in its target sort (`InjIn`). -/
  theorem rhsSort_sig : ∀ {t : Term} {s : Srt}, injFree t = true ∨ InjIn c I →
      sortOfTerm (c.rhsCtx L) vars t = some s →
      (∀ i ∈ varOccs t, InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (keyAt vs i)))) →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret I e m → InS I (c.sortName s) m
    | .var i, s, _, ht, hin, m, hm => by
      have hi := sortOfTerm_var.mp ht
      rw [tr_var] at hm
      rw [hm]
      have := hin i (by simp [varOccs])
      rwa [List.getD_eq_getElem?_getD, hi, Option.getD_some] at this
    | .dv s' lit, s, _, ht, _, m, hm => by
      obtain ⟨hok, rfl⟩ := sortOfTerm_dv.mp ht
      obtain ⟨σ, hσ, hσS⟩ := TieRhs.sortSing_sig hD hSig (hvn hok)
      rw [Term.kore] at hm
      unfold srtOf at hm
      rw [KoreAML.tr_dv] at hm
      have hit : I ⊧ᴵ (KoreAML.dvArityItem lit.text).pat := hSig _ (Or.inr ⟨lit.text, rfl⟩)
      have h1 := hit ⟨fun _ => σ, fun _ _ => False⟩ default
      have h1' : (KoreAML.guarded [KoreAML.sortGuard (⟨1⟩ : EVar)]
          (KoreAML.sym (.dv lit.text) ⬝ .evar ⟨1⟩ ⊆⊆ KoreAML.inhOf (.evar ⟨1⟩))).interpret I
          ⟨fun _ => σ, fun _ _ => False⟩ default := h1
      have h2 := interp_guarded h1' (fun w hw => by
        rw [List.mem_singleton.mp hw]
        unfold KoreAML.sortGuard
        rw [KoreAML.interp_member hD, KoreAML.interp_sortsDomain]
        exact hσS)
      rw [KoreAML.interp_included hD] at h2
      obtain ⟨d, x, hd, hx, happ⟩ := KoreAML.interp_app.mp hm
      have hxσ : x = σ := (hσ x).mp hx
      subst hxσ
      have h3 := h2 m (KoreAML.interp_app.mpr ⟨d, x, hd, rfl, happ⟩)
      rw [KoreAML.interp_inhOf_of (fun a => KoreAML.interp_evar)] at h3
      exact (KoreAML.interp_inhOf_of (S := KoreAML.Cons.sortP (c.sortName s)) (e := KoreAML.val0)
        (fun a => hσ a)).mpr h3
    | .app f ts, s, hf, ht, hin, m, hm => by
      obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
      obtain ⟨hkm, hkn⟩ := lookupSig_spec hk'
      rw [kore_app, tr_symApp, trArgs_appList, interp_appList] at hm
      obtain ⟨a, ha, bs, hbs, hm⟩ := hm
      have hf' : injFreeList ts = true ∨ InjIn c I := hf.imp (fun h => by rw [injFree] at h; exact h) id
      have hsorts := rhsSorts_sig hf' hargs (fun i hi => hin i (by rw [varOccs]; exact hi)) hbs
      subst hkn
      exact head_arity_sig hD hSig (Model.rhsHead_kernel hL hkm) ha hsorts.1 hsorts.2 hm
    | .inj a b t, s, hf, ht, hin, m, hm => by
      rcases hf with hf | hj
      · rw [injFree] at hf; cases hf
      · obtain ⟨hab, ht', rfl⟩ := sortOfTerm_inj.mp ht
        rw [Term.kore, KoreAML.tr_injP, interp_injApp] at hm
        obtain ⟨x, hx, hm⟩ := hm
        exact hj hab (rhsSort_sig (.inr hj) ht' (fun i hi => hin i (by rw [varOccs]; exact hi)) x hx) hm
    | .as _ _, s, _, ht, _, _, _ => absurd ht Model.sortOfTerm_rhs_as
  theorem rhsSorts_sig : ∀ {ts : List Term} {ss : List Srt} {bs : List M}, injFreeList ts = true ∨ InjIn c I →
      sortsOfTerms (c.rhsCtx L) vars ts = some ss →
      (∀ i ∈ varOccsList ts, InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (keyAt vs i)))) →
      All2 (fun φ b => φ.interpret I e b) ((Term.koreList c vs ts).map (KoreAML.tr ⟨tbl, []⟩)) bs →
      bs.length = (ss.map c.sortName).length ∧
        ∀ (i : Nat) x s, bs[i]? = some x → (ss.map c.sortName)[i]? = some s → InS I s x
    | [], ss, bs, _, ht, _, hbs => by
      rw [sortsOfTerms_nil.mp ht]
      rw [Term.koreList] at hbs
      cases hbs
      exact ⟨rfl, fun i x s h _ => by simp at h⟩
    | t :: ts, ss, bs, hf, ht, hin, hbs => by
      obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOfTerms_cons.mp ht
      have hf1 : injFree t = true ∨ InjIn c I :=
        hf.imp (fun h => by rw [injFreeList, Bool.and_eq_true] at h; exact h.1) id
      have hf2 : injFreeList ts = true ∨ InjIn c I :=
        hf.imp (fun h => by rw [injFreeList, Bool.and_eq_true] at h; exact h.2) id
      rw [Term.koreList, List.map_cons] at hbs
      cases hbs with
      | cons hb hbs =>
        have ih := rhsSorts_sig hf2 h2 (fun i hi => hin i (by rw [varOccsList]; exact List.mem_append_right _ hi)) hbs
        refine ⟨by simp [ih.1], fun i x s' hx hs' => ?_⟩
        cases i with
        | zero =>
          simp at hx hs'; subst hx; subst hs'
          exact rhsSort_sig hf1 h1 (fun i hi => hin i (by rw [varOccsList]; exact List.mem_append_left _ hi)) _ hb
        | succ i => exact ih.2 i x s' (by simpa using hx) (by simpa using hs')
end

end

/-- **`TermsInSortNI` in a model of definedness and the signature**, the sort of each value of the
definition being numbered. -/
theorem termsInSortNI_of_sig {c : Semantics} [OvlOK c] {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hD : DefOK I) (hSig : I ⊧ᴵP ΓSig c)
    (hvn : ∀ {v : GroundTerm} {s : Srt}, c.sortOf v = some s → s < nRegSorts + c.sortNames.length) :
    TermsInSortNI c I :=
  fun hni ht _ hin a ha =>
    rhsSort_sig hD hSig (fun hok => hvn (sortOf_dv.mpr ⟨hok, rfl⟩)) fns_headsOK (.inl hni) ht hin a ha

/-- **`Faithful.TermsInSort` in a model of definedness and the signature in which each injection puts
its source sort's elements in its target sort** (`InjIn`; `injIn_of_arity` gives it from `inj`'s
arity item), the sort of each value of the definition being numbered. -/
theorem termsInSort_of_sig_inj {c : Semantics} [OvlOK c] {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hD : DefOK I) (hSig : I ⊧ᴵP ΓSig c)
    (hvn : ∀ {v : GroundTerm} {s : Srt}, c.sortOf v = some s → s < nRegSorts + c.sortNames.length)
    (hj : InjIn c I) : TermsInSort c I :=
  fun ht _ hin a ha =>
    rhsSort_sig hD hSig (fun hok => hvn (sortOf_dv.mpr ⟨hok, rfl⟩)) fns_headsOK (.inr hj) ht hin a ha

/-- The two for a definition `coreOK` accepts. -/
theorem sig_of_core {c : Semantics} (h : c.coreOK = true) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hD : DefOK I) (hSig : I ⊧ᴵP ΓSig c) : SigFacts c I ∧ TermsInSortNI c I :=
  haveI : OvlOK c := (hypSound_of_core h).2.2.2.2.2.2.2.2
  ⟨sigFacts_of_sig hD hSig, termsInSortNI_of_sig hD hSig
    (fun hv => sortOf_numbered_of (hypSound_of_core h) (sortsNumbered_of_core h) (Semantics.coreOK_ovls h) hv)⟩

/-- The two for a definition `coreOK` accepts, in a model of `inj`'s arity item also: `SigFacts`
and `Faithful.TermsInSort`, for every term. -/
theorem sig_of_core_inj {c : Semantics} (h : c.coreOK = true) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hD : DefOK I) (hSig : I ⊧ᴵP ΓSig c) (hA : I ⊧ᴵ injArityP) : SigFacts c I ∧ TermsInSort c I := by
  haveI : OvlOK c := (hypSound_of_core h).2.2.2.2.2.2.2.2
  have hn := sortsNumbered_of_core h
  simp only [Model.sortsNumbered, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hn
  exact ⟨sigFacts_of_sig hD hSig, termsInSort_of_sig_inj hD hSig
    (fun hv => sortOf_numbered_of (hypSound_of_core h) (sortsNumbered_of_core h) (Semantics.coreOK_ovls h) hv)
    (injIn_of_arity hD hSig (fun hab => hn.1.1.2 _ hab) hA)⟩

/-- `sig_of_core_inj` in the form the lemmas below take, at the decision that accepts every term:
with it their premises on the terms read are `fun _ _ => rfl`, `rfl` and `tightOnB_all`. -/
theorem sig_of_core_all {c : Semantics} (h : c.coreOK = true) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hD : DefOK I) (hSig : I ⊧ᴵP ΓSig c) (hA : I ⊧ᴵ injArityP) :
    SigFacts c I ∧ TermsInSortOn (fun _ => true) c I :=
  have h2 := sig_of_core_inj h hD hSig hA
  ⟨h2.1, fun _ ht hs hin a ha => h2.2 ht hs hin a ha⟩

variable {ok : Term → Bool}


/-! ## The readings (KcoreSpec/TieFRRead.lean), with `SigFacts` -/

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

section
variable [Inhabited M] {c : Semantics} (F : SigFacts c I) {tbl : VarTable} {vs : List KoreAML.Var}
  {e : Valuation M} {m : M}
include F

omit [Inhabited M] in
theorem boolDen_of_sig : BoolDen I := by
  obtain ⟨β, hβ, hβd⟩ := F.sort (Faithful.bool_numbered (c := c))
  refine ⟨β, hβ, fun e a => ?_⟩
  have := hβd [] e a
  rwa [srtOf, Faithful.sortName_bool, Faithful.trSort_srt] at this

omit [Inhabited M] in
/-- A conjunction of conditions, at an element of the sort variable's sort, holds where each does. -/
theorem condKore_conjC_sig (hm : Inh I (e.evalEvar (tbl.ev (sortVarKey Rv))) m) : ∀ ps : List Cond,
    (tr ⟨tbl, []⟩ (Cond.kore c vs R (Parse.conjC ps))).interpret I e m ↔
      ∀ p ∈ ps, (tr ⟨tbl, []⟩ (Cond.kore c vs R p)).interpret I e m
  | [] => by
    rw [Parse.conjC, Cond.kore, tr_top_iff F.defOK (by rw [TieFRRead.trSort_R]; exact fun _ => interp_evar)]
    exact ⟨fun _ p hp => absurd hp List.not_mem_nil, fun _ => hm⟩
  | [p] => by
    rw [Parse.conjC]
    simp only [List.mem_singleton, forall_eq]
  | p :: q :: qs => by
    show (tr ⟨tbl, []⟩ (Cond.kore c vs R (.and p (Parse.conjC (q :: qs))))).interpret I e m ↔ _
    rw [Cond.kore, Faithful.tr_and2, interp_sAnd, condKore_conjC_sig hm (q :: qs)]
    simp

/-- `⌈t⌉` at an element of the sort variable's sort: t is defined. -/
theorem condKore_ceil_sig {s : Srt} {σ : M} {t : Term}
    (hσ : ∀ a, (trSort tbl (srtOf c s)).interpret I e a ↔ a = σ) (hσS : IsSort I σ)
    (hr : IsSort I (e.evalEvar (tbl.ev (sortVarKey Rv)))) (hm : Inh I (e.evalEvar (tbl.ev (sortVarKey Rv))) m)
    (hφ : ∀ b, (tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret I e b → Inh I σ b) :
    (tr ⟨tbl, []⟩ (Cond.kore c vs R (.ceil s t))).interpret I e m ↔ ∃ b, (tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret I e b := by
  rw [Cond.kore, tr, TieFRRead.trSort_R, interp_sCeil F.defOK F.ceilDef hσ (fun _ => interp_evar) hσS hr hφ m]
  exact ⟨fun h => h.1, fun h => ⟨h, hm⟩⟩

/-- `b = true` at an element of the sort variable's sort: b agrees with `true` on Bool. -/
theorem condKore_isTrue_sig {b : Term} (hr : IsSort I (e.evalEvar (tbl.ev (sortVarKey Rv))))
    (hm : Inh I (e.evalEvar (tbl.ev (sortVarKey Rv))) m) :
    (tr ⟨tbl, []⟩ (Cond.kore c vs R (Parse.isTrueC b))).interpret I e m ↔ EqTrue I e (tr ⟨tbl, []⟩ (Term.kore c vs b)) := by
  obtain ⟨β, hβ, hβd⟩ := boolDen_of_sig F
  have hT : tr ⟨tbl, []⟩ (Cond.kore c vs R (Parse.isTrueC b)) =
      sEquals boolP (.evar (tbl.ev (sortVarKey Rv))) (tr ⟨tbl, []⟩ (Term.kore c vs b)) trueP := by
    rw [Parse.isTrueC, Cond.kore, tr, ← TieFRRead.trSort_R, tr_boolT]
    simp only [srtOf, Faithful.sortName_bool, Faithful.trSort_srt]
    rfl
  rw [hT, interp_sEquals F.defOK F.ceilDef (hβd e) (fun _ => interp_evar) hβ hr]
  unfold EqTrue
  simp only [interp_inhOf_of (hβd e), hm, true_and]

/-- An alternative's predicate, at an element of the sort variable's sort: its term is defined and
its Bool terms agree with `true`. -/
theorem preOf_iff_sig {s : Srt} {σ : M} {x : Term × List Term}
    (hσ : ∀ a, (trSort tbl (srtOf c s)).interpret I e a ↔ a = σ) (hσS : IsSort I σ)
    (hr : IsSort I (e.evalEvar (tbl.ev (sortVarKey Rv)))) (hm : Inh I (e.evalEvar (tbl.ev (sortVarKey Rv))) m)
    (hφ : ∀ b, (altP c tbl vs x).interpret I e b → Inh I σ b) :
    (tr ⟨tbl, []⟩ (Cond.kore c vs R (preOf s x))).interpret I e m ↔
      (∃ b, (altP c tbl vs x).interpret I e b) ∧ altG I c tbl vs x e := by
  unfold preOf
  rw [condKore_conjC_sig F hm]
  simp only [List.mem_cons, List.mem_map, forall_eq_or_imp, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  rw [condKore_ceil_sig F hσ hσS hr hm hφ]
  simp only [condKore_isTrue_sig F hr hm]
  rfl

end

section
variable [Inhabited M] {c : Semantics} (F : SigFacts c I)
include F

/-- **The readings of the clauses `frClauses` writes** (`TieFR.Readings`). For the alternatives
`xs` over the variables `vs`, with the premise `prem` of the sentence: each clause's premise
(`clauseQ`, `lastQ`) reads from `NodeFacts`; that each alternative lies in the result sort σ is
`hin` (`inSort_of_terms_sig` gives it from `TermsInSortOn`); the reading of the sentence's right side is
`hrhs` (`readings_of_fr_sig` gives it from the reader). -/
theorem readings_of_rhs_sig {tbl : VarTable} {vs : List KoreAML.Var} {s : Srt} {xs : List (Term × List Term)}
    {ws : List KoreAML.P} {σ : M} {prem rhsT : KoreAML.P}
    (hr : sortGuard (tbl.ev (sortVarKey Rv)) ∈ ws)
    (hσ : ∀ (e : Valuation M) a, (trSort tbl (srtOf c s)).interpret I e a ↔ a = σ) (hσS : IsSort I σ)
    (hin : ∀ e m, TieFR.At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ x ∈ xs, ∀ a,
      (altP c tbl vs x).interpret I e a → Inh I σ a)
    (hrhs : ∀ e m, TieFR.At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ a, Inh I σ a →
      (rhsT.interpret I e a ↔ ∃ x ∈ xs, (altP c tbl vs x).interpret I e a ∧ altG I c tbl vs x e)) :
    TieFR.Readings I ws (tbl.ev (sortVarKey Rv)) σ prem rhsT xs (altP c tbl vs) (altG I c tbl vs)
      (clauseQ c tbl vs s prem) (lastQ c tbl vs s prem xs) where
  inSort := hin
  clause e m hat x hx := by
    have hrS := TieFR.isSort_of_at F.defOK hr hat
    unfold clauseQ
    rw [interp_sAnd, preOf_iff_sig F (hσ e) hσS hrS hat.2 (hin e m hat x hx)]
  none e m hat := by
    have hrS := TieFR.isSort_of_at F.defOK hr hat
    unfold lastQ preN
    rw [interp_sAnd, condKore_conjC_sig F hat.2]
    refine and_congr Iff.rfl ?_
    simp only [List.forall_mem_map]
    refine forall_congr' fun x => forall_congr' fun hx => ?_
    rw [condKore_not, preOf_iff_sig F (hσ e) hσS hrS hat.2 (hin e m hat x hx)]
    exact ⟨fun h => h.1, fun h => ⟨h, hat.2⟩⟩
  rhs := hrhs

/-- **The readings of the clauses `frClauses` writes, from the reader** (`TieFR.Readings`). The
equation `eq` is one `frRead` reads as clauses, its right side `eq.rhs` translated over the text's
table `tblT`, and its `ensures` part `en` holding where `Ens` does. What `frRead` checks of the
right side gives its normalisation `hoist (dropEmptyAlts eq.rhs)` (`frSide`, with the conditions
`frConds`), not empty, and that every lifted condition is that a Bool term be `true`
(`frRead_norm`); the sorts of its connectives are the reader's: `frRead` reads only a right side
that is `rhsSorted` (`frRead_rhsSorted`), which with `TightSem` (its operands lie in their sorts)
is `Tight` (`tight_of_rhsSorted`). The reading of the right side is then `rhs_of_reader`'s, the
rest `readings_of_rhs_sig`'s. -/
theorem readings_of_fr_sig {N : Parse.Names} {eq : Parse.RawEqn} {z : List Clause × List KoreAML.Var}
    {tbl tblT : VarTable} {vs : List KoreAML.Var} {s : Srt} {xs : List (Term × List Term)}
    {ws : List KoreAML.P} {σ : M} {prem : KoreAML.P} {en : Kore.Pattern}
    {Ens : Valuation M → Prop}
    (hrd : Parse.frRead N eq = .ok (some z))
    (hr : sortGuard (tbl.ev (sortVarKey Rv)) ∈ ws)
    (hσ : ∀ (e : Valuation M) a, (trSort tbl (srtOf c s)).interpret I e a ↔ a = σ) (hσS : IsSort I σ)
    (hin : ∀ e m, TieFR.At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ x ∈ xs, ∀ a,
      (altP c tbl vs x).interpret I e a → Inh I σ a)
    (hT : ∀ e m, TieFR.At I ws (tbl.ev (sortVarKey Rv)) e m → TightSem I tblT e eq.rhs)
    (hen : ∀ e m, TieFR.At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ a, Inh I σ a →
      ((tr ⟨tblT, []⟩ en).interpret I e a ↔ Ens e))
    (hbr : All2 (fun k x =>
      (∀ e m, TieFR.At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ a,
        (altP c tbl vs x).interpret I e a ↔ (tr ⟨tblT, []⟩ k.1).interpret I e a) ∧
      ∀ e m, TieFR.At I ws (tbl.ev (sortVarKey Rv)) e m →
        (altG I c tbl vs x e ↔ Ens e ∧ HoldsSC I tblT e (frConds eq.rhs) ∧ HoldsSC I tblT e k.2))
      (keptAlts (frSide eq.rhs)) xs) :
    TieFR.Readings I ws (tbl.ev (sortVarKey Rv)) σ prem
      (sAnd (tr ⟨tblT, []⟩ eq.rhs) (tr ⟨tblT, []⟩ en)) xs (altP c tbl vs) (altG I c tbl vs)
      (clauseQ c tbl vs s prem) (lastQ c tbl vs s prem xs) :=
  have hn := frRead_norm hrd
  readings_of_rhs_sig F hr hσ hσS hin
    (rhs_of_reader F.defOK F.ceilDef (boolDen_of_sig F)
      (fun e m hat => tight_of_rhsSorted eq.rhs (Parse.frRead_rhsSorted hrd) (hT e m hat))
      hn.1 hn.2.1 hn.2.2 hen hbr)

omit F in
/-- **The alternatives lie in the result sort** where each is a term of it that `ok` accepts
(`TermsInSortOn`) and the guards put its variables in their sorts. -/
theorem inSort_of_terms_sig (hTS : TermsInSortOn ok c I) {tbl : VarTable} {vars : List Srt} {s : Srt}
    {xs : List (Term × List Term)} {ws : List KoreAML.P} {r : EVar} {σ : M}
    (hni : ∀ x ∈ xs, ok x.1 = true)
    (hs : s < nRegSorts + c.sortNames.length)
    (hσ : ∀ (e : Valuation M) a, (trSort tbl (srtOf c s)).interpret I e a ↔ a = σ)
    (hty : ∀ x ∈ xs, sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars x.1 = some s)
    (hvar : ∀ e m, TieFR.At I ws r e m → ∀ x ∈ xs, ∀ i ∈ varOccs x.1,
      Faithful.InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (Faithful.canonKey c vars i)))) :
    ∀ e m, TieFR.At I ws r e m → ∀ x ∈ xs, ∀ a, (altP c tbl (canonVars c vars) x).interpret I e a → Inh I σ a := by
  intro e m hat x hx a ha
  have h := hTS (hni x hx) (hty x hx) hs (hvar e m hat x hx) a ha
  rw [← Faithful.inS_iff e] at h
  have : KoreAML.Cons.sortP (c.sortName s) = trSort tbl (srtOf c s) := by
    rw [srtOf, Faithful.trSort_srt]; rfl
  rw [this, interp_inhOf_of (hσ e)] at h
  exact h


end

/-- **An operand that translates as a term of the sort s lies in s** (`TermsInSortOn`, `ok` accepting the term), where the
valuation puts the term's variables in their sorts. -/
theorem inSortK_of_term_sig [Inhabited M] {c : Semantics} (hTS : TermsInSortOn ok c I) {tbl tblT : VarTable}
    {vars : List Srt} {s : Srt} {t : Term} {S : Kore.KSort} {q : Kore.Pattern} {e : Valuation M}
    (hni : ok t = true)
    (hs : s < nRegSorts + c.sortNames.length) (hty : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t = some s)
    (htr : tr ⟨tblT, []⟩ q = tr ⟨tbl, []⟩ (Term.kore c (canonVars c vars) t))
    (hS : trSort tblT S = trSort tbl (srtOf c s))
    (hvar : ∀ i ∈ varOccs t, Faithful.InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (Faithful.canonKey c vars i)))) :
    InSortK I tblT e S q := by
  intro a ha
  rw [htr] at ha
  have h := hTS hni hty hs hvar a ha
  rw [← Faithful.inS_iff e] at h
  have : KoreAML.Cons.sortP (c.sortName s) = trSort tbl (srtOf c s) := by
    rw [srtOf, Faithful.trSort_srt]; rfl
  rw [hS, ← this]
  exact h

/-! ### Competitors -/


section
variable [Inhabited M] {c : Semantics} (F : SigFacts c I)
include F

/-- **The readings of the clauses `frClauses` writes, from the text's literal** (`TieFR.Readings`).
`readings_of_fr_sig` with: the text's translation naming the aliases `al`, which its right side and
`ensures` part do not apply (`tr_aliasFree`); the `ensures` part read by `ensBools`, holding all of
its sort σ where its Bool terms agree with `true` (`ens_reading`); and the pairing of the
alternatives with the kept ones decided on the literal (`altsTrOK`, `all2_of_altsTrOK`). What is
left is `TightSem` (`tightSem_of_ops`) and that the alternatives lie in σ (`inSort_of_terms_sig`). -/
theorem readings_of_frT_sig {N : Parse.Names} {eq : Parse.RawEqn} {z : List Clause × List KoreAML.Var}
    {al : List String} {tbl tblT : VarTable} {vs : List KoreAML.Var} {s : Srt} {xs : List (Term × List Term)}
    {ws : List KoreAML.P} {σ : M} {prem : KoreAML.P} {en : Kore.Pattern} {bs : List Kore.Pattern}
    (hrd : Parse.frRead N eq = .ok (some z))
    (hal : aliasFreeFR al eq.rhs = true) (hal' : aliasFreeFR al en = true)
    (hr : sortGuard (tbl.ev (sortVarKey Rv)) ∈ ws)
    (hσ : ∀ (e : Valuation M) a, (trSort tbl (srtOf c s)).interpret I e a ↔ a = σ) (hσS : IsSort I σ)
    (hin : ∀ e m, TieFR.At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ x ∈ xs, ∀ a,
      (altP c tbl vs x).interpret I e a → Inh I σ a)
    (hT : ∀ e m, TieFR.At I ws (tbl.ev (sortVarKey Rv)) e m → TightSem I tblT e eq.rhs)
    (hE : ensBools en = some bs)
    (hES : ∀ (e : Valuation M) a, (trSort tblT (ensSort en)).interpret I e a ↔ a = σ)
    (hok : altsTrOK c tbl vs tblT (frConds eq.rhs) bs (keptAlts (frSide eq.rhs)) xs = true) :
    TieFR.Readings I ws (tbl.ev (sortVarKey Rv)) σ prem
      (sAnd (tr ⟨tblT, al⟩ eq.rhs) (tr ⟨tblT, al⟩ en)) xs (altP c tbl vs) (altG I c tbl vs)
      (clauseQ c tbl vs s prem) (lastQ c tbl vs s prem xs) := by
  rw [tr_aliasFree tblT al _ hal, tr_aliasFree tblT al _ hal']
  exact readings_of_fr_sig F (Ens := fun e => ∀ b ∈ bs, EqTrue I e (tr ⟨tblT, []⟩ b)) hrd hr hσ hσS hin hT
    (fun e _ _ a ha => ens_reading F.defOK F.ceilDef (boolDen_of_sig F) hE hES hσS e a ha)
    (all2_of_altsTrOK hok)

end

end

/-! ## The decision (KcoreSpec/TieFRTightB.lean), with `SigFacts` and `TermsInSortOn` -/

/-- **An operand read as a term of the sort s lies in s** (`inSortK_of_term_sig`, its translation
from the round trip), `ok` accepting the term. -/
theorem inSortK_of_read_sig {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} {N : Parse.Names} {c : Semantics}
    (hsy : N.syms = c.symNames) (hso : N.sorts = c.sortNames) (hTS : TermsInSortOn ok c I)
    {tbl tblT : VarTable} {vars : List Srt} {vsF vs vs' : List Var} (hA : alignOK c tbl tblT vars vsF = true)
    {s : Srt} {t : Term} {S : Kore.KSort} {q : Kore.Pattern} {e : Valuation M}
    (hrd : Parse.term N vs q = .ok (t, vs')) (hni : ok t = true) (hrt : rtPat N q = true) (hp : vs' <+: vsF)
    (hs : s < nRegSorts + c.sortNames.length) (hty : sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t = some s)
    (hS : trSort tblT S = trSort tbl (srtOf c s))
    (hvar : ∀ i ∈ varOccs t, Faithful.InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (Faithful.canonKey c vars i)))) :
    InSortK I tblT e S q :=
  inSortK_of_term_sig hTS hni hs hty (term_rt hsy hso hA hrd hrt hp) hS hvar

/-- `ok` accepts the term `Parse.term` reads of q over `vsF`. -/
def termOnB (ok : Term → Bool) (N : Parse.Names) (vsF : List Var) (q : Kore.Pattern) : Bool :=
  match Parse.term N vsF q with
  | .ok (t, _) => ok t
  | .error _ => true

/-- An operand that `leafInB` reads as terms: each of its alternatives is read as a term `ok`
accepts. -/
def leafOnB (ok : Term → Bool) (N : Parse.Names) (vsF : List Var) (x : Kore.KSort × Kore.Pattern) : Bool :=
  !opLeaf x.2 || opStatedK x.2 || (Parse.orAlts x.2).all (termOnB ok N vsF)

/-- `ok` accepts the terms `tightB` reads of p. -/
def tightOnB (ok : Term → Bool) (N : Parse.Names) (vsF : List Var) (p : Kore.Pattern) : Bool :=
  (connOps p).all (leafOnB ok N vsF)

/-- The term `Parse.term` reads of q over `vsF` holds no injection. -/
def termNIB (N : Parse.Names) (vsF : List Var) (q : Kore.Pattern) : Bool := termOnB injFree N vsF q

/-- An operand that `leafInB` reads as terms: each of its alternatives is read as a term that holds
no injection. -/
def leafNIB (N : Parse.Names) (vsF : List Var) (x : Kore.KSort × Kore.Pattern) : Bool := leafOnB injFree N vsF x

/-- The terms `tightB` reads of p hold no injection. -/
def tightNIB (N : Parse.Names) (vsF : List Var) (p : Kore.Pattern) : Bool := tightOnB injFree N vsF p

/-- Where `ok` accepts every term, the decision holds of every pattern: with `Faithful.TermsInSort`
(`termsInSortOn_of`) the lemmas below take no condition on the terms read. -/
theorem tightOnB_all (N : Parse.Names) (vsF : List Var) (p : Kore.Pattern) :
    tightOnB (fun _ => true) N vsF p = true := by
  unfold tightOnB
  refine List.all_eq_true.mpr fun x _ => ?_
  have h : (Parse.orAlts x.2).all (termOnB (fun _ => true) N vsF) = true :=
    List.all_eq_true.mpr fun q _ => by unfold termOnB; split <;> rfl
  unfold leafOnB
  rw [h, Bool.or_true]

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The alternatives lie in the function's result sort** (`TieFRVars.inSort_of_read`), `ok`
accepting each. -/
theorem inSort_of_read_sig {N : Parse.Names} {c : Semantics} (hD : DefOK I) (hTS : TermsInSortOn ok c I)
    (hso : N.sorts = c.sortNames) {tbl tblT : VarTable} {vars : List Srt} {vsF : List Var}
    (hvars : Parse.varSorts N vsF = .ok vars) (hA : alignOK c tbl tblT vars vsF = true)
    {ws : List P} {r : EVar} (hg : TieFRVars.guardsHold ws tblT vsF = true)
    {f : Fn} {s : Srt} {pats : List Term} {req : Option Term} {prio : Nat} {aside : Bool}
    {xs : List (Term × List Term)} (hni : ∀ x ∈ xs, ok x.1 = true)
    (hcs : ∀ cl ∈ Parse.frClauses s vars pats req prio aside (frAltsOf xs),
      c.clauseSorted f (c.fns.map Fn.sig) cl = true)
    (hs : f.result < nRegSorts + c.sortNames.length) {σ : M}
    (hσ : ∀ (e : Valuation M) a, (trSort tbl (srtOf c f.result)).interpret I e a ↔ a = σ) :
    ∀ e m, TieFR.At I ws r e m → ∀ x ∈ xs, ∀ a, (altP c tbl (canonVars c vars) x).interpret I e a → Inh I σ a :=
  inSort_of_terms_sig hTS hni hs hσ (TieFRVars.sorted_of_frClauses hcs).1
    (fun _ _ hat x hx => TieFRVars.hvar_of_sorted hD hso hvars hA hg hat.1 ((TieFRVars.sorted_of_frClauses hcs).1 x hx))

omit [Inhabited M] in
/-- A numbered sort's name denotes one sort. -/
theorem sortDen_of_sortNumB_sig {c : Semantics} (F : SigFacts c I) {tbl tblT : VarTable} {S : Kore.KSort}
    (h : sortNumB c tbl tblT S = true) (e : Valuation M) : SortDen I tblT e S := by
  obtain ⟨s, hs, hS⟩ := List.any_eq_true.mp h
  obtain ⟨τ, hτ, hd⟩ := F.sort (List.mem_range.mp hs)
  exact ⟨τ, hτ, fun a => by rw [of_decide_eq_true hS]; exact hd tbl e a⟩

/-- **A term of the sort S lies in S** (`termInB`), at a valuation that puts the variables of
`vars` in their sorts. -/
theorem inSortK_of_termInB_sig {N : Parse.Names} {c : Semantics} (hTS : TermsInSortOn ok c I)
    (hsy : N.syms = c.symNames) (hso : N.sorts = c.sortNames) {tbl tblT : VarTable} {vars : List Srt}
    {vsF : List Var} (hA : alignOK c tbl tblT vars vsF = true) {e : Valuation M}
    (hV : ∀ i < vars.length, InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (canonKey c vars i))))
    {S : Kore.KSort} {q : Kore.Pattern} (h : termInB N c tbl tblT vars vsF S q = true)
    (hni : termOnB ok N vsF q = true) : InSortK I tblT e S q := by
  unfold termInB at h
  unfold termOnB at hni
  split at h
  · rename_i t vs' hrd
    rw [hrd] at hni
    split at h
    · rename_i s hty
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hvs, hrt⟩, hs, hS⟩ := h
      have hvs' : vs' = vsF := varKeys_inj hvs
      exact inSortK_of_read_sig hsy hso hTS hA hrd hni hrt (hvs' ▸ List.prefix_refl _) hs hty hS
        (fun i hi => hV i (varOccs_lt t hty i hi))
    · simp at h
  · cases h

/-- **`TightSem` from the decision**, at a valuation that puts the variables of `vars` in their
sorts. -/
theorem tightSem_of_tightB_sig {N : Parse.Names} {c : Semantics} (F : SigFacts c I)
    (hTS : TermsInSortOn ok c I) (hsy : N.syms = c.symNames) (hso : N.sorts = c.sortNames)
    {tbl tblT : VarTable} {vars : List Srt} {vsF : List Var} (hA : alignOK c tbl tblT vars vsF = true)
    {e : Valuation M}
    (hV : ∀ i < vars.length, InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (canonKey c vars i))))
    {p : Kore.Pattern} (h : tightB N c tbl tblT vars vsF p = true) (hNI : tightOnB ok N vsF p = true) :
    TightSem I tblT e p := by
  have hD := F.defOK
  unfold tightB at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hS, hL⟩, hA'⟩ := h
  -- an operand that is no `\or` and no `\and` lies in its connective's sort where it is `TightSem`
  have hleaf : ∀ (s : Kore.KSort) (q : Kore.Pattern), (s, q) ∈ connOps p → opLeaf q = true →
      TightSem I tblT e q → InSortK I tblT e s q := by
    intro s q hx hlf hT
    have hl := hL (s, q) hx
    unfold leafInB at hl
    simp only [hlf, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true] at hl
    have hn := List.all_eq_true.mp hNI (s, q) hx
    unfold leafOnB at hn
    simp only [hlf, Bool.not_true, Bool.false_or, Bool.or_eq_true, List.all_eq_true] at hn
    rcases hl with hk | ⟨hrs, halts⟩
    · exact inSortK_of_stated hD q ((connOps_sub p (s, q) hx).2 hS) hk
    · rcases hn with hk | hn
      · exact inSortK_of_stated hD q ((connOps_sub p (s, q) hx).2 hS) hk
      · exact inSortK_of_alts hD (tight_of_rhsSorted q hrs hT)
          (fun q' hq' => inSortK_of_termInB_sig hTS hsy hso hA hV (halts q' hq') (hn q' hq'))
  suffices key : ∀ q, connOps q ⊆ connOps p → andSorts q ⊆ andSorts p →
      TightSem I tblT e q ∧ ∀ s, (s, q) ∈ connOps p → InSortK I tblT e s q from
    (key p (fun _ h => h) (fun _ h => h)).1
  intro q
  induction q using Kore.Pattern.rec
    (motive_2 := fun ps => ∀ q ∈ ps, connOps q ⊆ connOps p → andSorts q ⊆ andSorts p →
      TightSem I tblT e q ∧ ∀ s, (s, q) ∈ connOps p → InSortK I tblT e s q) with
  | app hd ss ps ih =>
    intro h1 h2
    have hT : TightSem I tblT e (.app hd ss ps) := by
      rw [TightSem, tightSemList_iff]
      intro q hq
      refine (ih q hq (fun y hy => h1 ?_) (fun y hy => h2 ?_)).1
      · rw [connOps, mem_connOpsList]; exact ⟨q, hq, hy⟩
      · rw [andSorts, mem_andSortsList]; exact ⟨q, hq, hy⟩
    exact ⟨hT, fun s hx => hleaf s _ hx rfl hT⟩
  | and s' ps ih =>
    intro h1 h2
    have hops : ∀ q ∈ ps, TightSem I tblT e q ∧ InSortK I tblT e s' q := by
      intro q hq
      have hq1 : (s', q) ∈ connOps (.and s' ps) := by
        rw [connOps, List.mem_append]; exact .inl (List.mem_map.mpr ⟨q, hq, rfl⟩)
      have := ih q hq (fun y hy => h1 (by rw [connOps, List.mem_append, mem_connOpsList]; exact .inr ⟨q, hq, hy⟩))
        (fun y hy => h2 (by rw [andSorts, List.mem_cons, mem_andSortsList]; exact .inr ⟨q, hq, hy⟩))
      exact ⟨this.1, this.2 s' (h1 hq1)⟩
    refine ⟨?_, fun s hx => ?_⟩
    · rw [TightSem, tightSemList_iff]
      exact ⟨sortDen_of_sortNumB_sig F (hA' s' (h2 (by rw [andSorts]; exact List.mem_cons_self ..))) e,
        fun q hq => (hops q hq).2, fun q hq => (hops q hq).1⟩
    · have hs := (connOps_sub p (s, .and s' ps) hx).2 hS
      rw [sortIs, Bool.and_eq_true, decide_eq_true_iff] at hs
      obtain ⟨rfl, -⟩ := hs
      exact inSortK_conn hD (.inr rfl) fun q hq => (hops q hq).2
  | or s' ps ih =>
    intro h1 h2
    have hops : ∀ q ∈ ps, TightSem I tblT e q ∧ InSortK I tblT e s' q := by
      intro q hq
      have hq1 : (s', q) ∈ connOps (.or s' ps) := by
        rw [connOps, List.mem_append]; exact .inl (List.mem_map.mpr ⟨q, hq, rfl⟩)
      have := ih q hq (fun y hy => h1 (by rw [connOps, List.mem_append, mem_connOpsList]; exact .inr ⟨q, hq, hy⟩))
        (fun y hy => h2 (by rw [andSorts, mem_andSortsList]; exact ⟨q, hq, hy⟩))
      exact ⟨this.1, this.2 s' (h1 hq1)⟩
    refine ⟨?_, fun s hx => ?_⟩
    · rw [TightSem, tightSemList_iff]
      exact ⟨fun q hq => (hops q hq).2, fun q hq => (hops q hq).1⟩
    · have hs := (connOps_sub p (s, .or s' ps) hx).2 hS
      rw [sortIs, Bool.and_eq_true, decide_eq_true_iff] at hs
      obtain ⟨rfl, -⟩ := hs
      exact inSortK_conn hD (.inl rfl) fun q hq => (hops q hq).2
  | nil => exact absurd ‹_ ∈ ([] : List Kore.Pattern)› List.not_mem_nil
  | cons q qs ih1 ih2 =>
    rename_i q' hq' h1 h2
    rcases List.mem_cons.mp hq' with rfl | hq'
    · exact ih1 h1 h2
    · exact ih2 q' hq' h1 h2
  | _ =>
    intro _ _
    refine ⟨by simp [TightSem], fun s hx => hleaf s _ hx rfl (by simp [TightSem])⟩

/-- **`TightSem` at the valuations of the guards** (`readings_of_frT_sig`'s `hT`): the guards hold
each variable read in its sort (`guardsHold`). -/
theorem tightSem_of_guardsB_sig {N : Parse.Names} {c : Semantics} (F : SigFacts c I)
    (hTS : TermsInSortOn ok c I) (hsy : N.syms = c.symNames) (hso : N.sorts = c.sortNames)
    {tbl tblT : VarTable} {vars : List Srt} {vsF : List Var}
    (hvars : Parse.varSorts N vsF = .ok vars) (hA : alignOK c tbl tblT vars vsF = true)
    {ws : List P} {r : EVar} (hg : TieFRVars.guardsHold ws tblT vsF = true)
    {p : Kore.Pattern} (h : tightB N c tbl tblT vars vsF p = true) (hNI : tightOnB ok N vsF p = true) :
    ∀ e m, TieFR.At I ws r e m → TightSem I tblT e p :=
  fun _ _ hat => tightSem_of_tightB_sig F hTS hsy hso hA
    (fun _ hi => TieFRVars.inS_of_guards F.defOK hso hvars hA hg hat.1
      (by rw [← (TieFRVars.varSorts_spec hvars).1]; exact hi)) h hNI

end

end TieFRSig

end KCore
