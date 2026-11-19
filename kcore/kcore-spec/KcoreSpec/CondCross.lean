/-
  KCore. A condition's predicate at the sort variable `R`.

  A clause's premise carries its predicate as `Cond.kore c vs R pre` (`withPre`), at the sort
  variable `R` of the equation, which a valuation may give any sort of the model. The Holds lemma
  (`HoldsDen'`) reads `Cond.kore c vs (srtOf c S) pre`, at a numbered sort `S` of the definition.
  The two patterns differ in the sort argument of each connective only, and a condition's pattern
  denotes the whole of that sort or nothing (`cond_predAt`), so whether it holds does not depend on
  the sort:
  - `\ceil{s,X}(t)`, `\in{s,X}(t, u)` and `\equals{s,X}(t, u)` are all of `X` where a fact about
    `t`, `u` at the sort `s` holds and empty where it does not (`interp_sCeil`, `interp_sIn`,
    `interp_sEquals`), and that fact does not mention `X`;
  - `\top`, `\bottom`, `\not`, `\and`, `\or`, `\implies` at `X` keep this, at the elements of `X`;
  - a binder ranges over the elements of its own sort, which is not `X`.
  `cond_crossAt` is the statement: at an element of the sort `R` is given and an element of the
  sort `S` denotes, the pattern at `R` holds at the first iff the pattern at `srtOf c S` holds at
  the second. It reads of the interpretation the sorts, the ceiling and that a well-sorted term's
  elements lie in its sort (`TermsInSort`: `condTerm_inh`'s fact, which every model of `Γ c` has,
  `termsInSort_of_model`). `holds_atR` is the Holds lemma at `R`, from the Holds lemma at the sort
  of the Booleans, which has an element.
-/
import KcoreSpec.CondPredAt
import KcoreSpec.HypWf
import KcoreSpec.FaithfulFamilies

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed VarKey VarTable)

/-! ## Two patterns that hold together, each at the elements of its sort -/

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- At the valuation e, φ holds at an element of the sort τ iff φ' holds at an element of the
sort τ'. `PredAt I τ φ e` is `CrossAt I τ τ φ φ e`. -/
def CrossAt (I : Interpretation KoreAML.Sym M) (τ τ' : M) (φ φ' : KoreAML.P) (e : Valuation M) : Prop :=
  ∀ m m', Inh I τ m → Inh I τ' m' → (φ.interpret I e m ↔ φ'.interpret I e m')

variable {τ τ' : M} {e : Valuation M} {s s' φ φ' ψ ψ' : KoreAML.P}

theorem crossAt_form {Q : Prop} (h : ∀ m, φ.interpret I e m ↔ Q ∧ Inh I τ m)
    (h' : ∀ m, φ'.interpret I e m ↔ Q ∧ Inh I τ' m) : CrossAt I τ τ' φ φ' e :=
  fun m m' hm hm' => by
    rw [h m, h' m']
    exact ⟨fun hq => ⟨hq.1, hm'⟩, fun hq => ⟨hq.1, hm⟩⟩

theorem crossAt_sNot (hs : ∀ a, s.interpret I e a ↔ a = τ) (hs' : ∀ a, s'.interpret I e a ↔ a = τ')
    (h : CrossAt I τ τ' φ φ' e) : CrossAt I τ τ' (KoreAML.sNot s φ) (KoreAML.sNot s' φ') e :=
  fun m m' hm hm' => by
    rw [KoreAML.interp_sNot, KoreAML.interp_sNot, KoreAML.interp_inhOf_of hs, KoreAML.interp_inhOf_of hs',
      h m m' hm hm']
    exact ⟨fun hq => ⟨hq.1, hm'⟩, fun hq => ⟨hq.1, hm⟩⟩

theorem crossAt_sAnd (h1 : CrossAt I τ τ' φ φ' e) (h2 : CrossAt I τ τ' ψ ψ' e) :
    CrossAt I τ τ' (KoreAML.sAnd φ ψ) (KoreAML.sAnd φ' ψ') e :=
  fun m m' hm hm' => by
    rw [KoreAML.interp_sAnd, KoreAML.interp_sAnd, h1 m m' hm hm', h2 m m' hm hm']

theorem crossAt_sOr (hs : ∀ a, s.interpret I e a ↔ a = τ) (hs' : ∀ a, s'.interpret I e a ↔ a = τ')
    (h1 : CrossAt I τ τ' φ φ' e) (h2 : CrossAt I τ τ' ψ ψ' e) :
    CrossAt I τ τ' (KoreAML.sOr s φ ψ) (KoreAML.sOr s' φ' ψ') e := fun m m' hm hm' => by
  rw [KoreAML.interp_sOr, KoreAML.interp_sOr, KoreAML.interp_inhOf_of hs, KoreAML.interp_inhOf_of hs',
    h1 m m' hm hm', h2 m m' hm hm']
  exact ⟨fun hq => ⟨hm', hq.2⟩, fun hq => ⟨hm, hq.2⟩⟩

theorem crossAt_sImp (hs : ∀ a, s.interpret I e a ↔ a = τ) (hs' : ∀ a, s'.interpret I e a ↔ a = τ')
    (h1 : CrossAt I τ τ' φ φ' e) (h2 : CrossAt I τ τ' ψ ψ' e) :
    CrossAt I τ τ' (KoreAML.sImp s φ ψ) (KoreAML.sImp s' φ' ψ') e := fun m m' hm hm' => by
  rw [KoreAML.interp_sImp, KoreAML.interp_sImp, KoreAML.interp_inhOf_of hs, KoreAML.interp_inhOf_of hs',
    h1 m m' hm hm', h2 m m' hm hm']
  exact ⟨fun hq => ⟨hm', hq.2⟩, fun hq => ⟨hm, hq.2⟩⟩

/-- One sorted binder over two bodies that hold together at each element of the binder's sort. -/
theorem crossAt_sExists (hD : DefOK I) {x : EVar} {sb : KoreAML.P} (hsb : Closed sb)
    (h : ∀ a, (KoreAML.inhOf sb).interpret I e a →
      CrossAt I τ τ' φ φ' ⟨Function.update e.evalEvar x a, e.evalSvar⟩) :
    CrossAt I τ τ' (KoreAML.sExists x sb φ) (KoreAML.sExists x sb φ') e := fun m m' hm hm' => by
  rw [KoreAML.interp_sExists, KoreAML.interp_sExists]
  simp only [KoreAML.interp_member hD, Function.update_same]
  constructor
  · rintro ⟨a, ha, hb⟩
    exact ⟨a, ha, (h a (((closed_inhOf_twoT hsb).interp _ e a).mp ha) m m' hm hm').mp hb⟩
  · rintro ⟨a, ha, hb⟩
    exact ⟨a, ha, (h a (((closed_inhOf_twoT hsb).interp _ e a).mp ha) m m' hm hm').mpr hb⟩

theorem tr_exist_resort {ctx : KoreAML.Ctx} (S : Kore.KSort) (x : Kore.EVar) (p : Kore.Pattern) :
    KoreAML.tr ctx (.exist S x p) =
      KoreAML.sExists (ctx.vars.ev (KoreAML.evarKey x)) (KoreAML.trSort ctx.vars x.sort) (KoreAML.tr ctx p) := by
  rw [KoreAML.tr]

theorem tr_forall_resort {ctx : KoreAML.Ctx} (S : Kore.KSort) (x : Kore.EVar) (p : Kore.Pattern) :
    KoreAML.tr ctx (.forall S x p) =
      KoreAML.sForall (KoreAML.trSort ctx.vars S) (ctx.vars.ev (KoreAML.evarKey x))
        (KoreAML.trSort ctx.vars x.sort) (KoreAML.tr ctx p) := by
  rw [KoreAML.tr]

theorem tr_not_resort {ctx : KoreAML.Ctx} (S : Kore.KSort) (p : Kore.Pattern) :
    KoreAML.tr ctx (.not S p) = KoreAML.sNot (KoreAML.trSort ctx.vars S) (KoreAML.tr ctx p) := by
  rw [KoreAML.tr]

theorem tr_implies_resort {ctx : KoreAML.Ctx} (S : Kore.KSort) (p q : Kore.Pattern) :
    KoreAML.tr ctx (.implies S p q) =
      KoreAML.sImp (KoreAML.trSort ctx.vars S) (KoreAML.tr ctx p) (KoreAML.tr ctx q) := by
  rw [KoreAML.tr]

theorem tr_top_resort {ctx : KoreAML.Ctx} (S : Kore.KSort) :
    KoreAML.tr ctx (.top S) = KoreAML.sTop (KoreAML.trSort ctx.vars S) := by
  rw [KoreAML.tr]

theorem tr_bottom_resort {ctx : KoreAML.Ctx} (S : Kore.KSort) :
    KoreAML.tr ctx (.bottom S) = KoreAML.sBot (KoreAML.trSort ctx.vars S) := by
  rw [KoreAML.tr]

theorem tr_ceil_resort {ctx : KoreAML.Ctx} (S S' : Kore.KSort) (p : Kore.Pattern) :
    KoreAML.tr ctx (.ceil S S' p) =
      KoreAML.sCeil (KoreAML.trSort ctx.vars S) (KoreAML.trSort ctx.vars S') (KoreAML.tr ctx p) := by
  rw [KoreAML.tr]

theorem tr_equals_resort {ctx : KoreAML.Ctx} (S S' : Kore.KSort) (p q : Kore.Pattern) :
    KoreAML.tr ctx (.equals S S' p q) =
      KoreAML.sEquals (KoreAML.trSort ctx.vars S) (KoreAML.trSort ctx.vars S') (KoreAML.tr ctx p)
        (KoreAML.tr ctx q) := by
  rw [KoreAML.tr]

theorem tr_in_resort {ctx : KoreAML.Ctx} (S S' : Kore.KSort) (p q : Kore.Pattern) :
    KoreAML.tr ctx (.in S S' p q) =
      KoreAML.sIn (KoreAML.trSort ctx.vars S) (KoreAML.trSort ctx.vars S') (KoreAML.tr ctx p)
        (KoreAML.tr ctx q) := by
  rw [KoreAML.tr]

variable [Inhabited M]

/-- `existsAll` at two sorts over two bodies that hold together at every valuation that differs
from e at the binders only and gives each binder an element of its sort. -/
theorem crossAt_existsAll (hD : DefOK I) {tbl : VarTable} {S S' : Kore.KSort} {body body' : Kore.Pattern} :
    ∀ (bs : List Kore.EVar) (e : Valuation M),
    (bs.map fun b => tbl.ev (KoreAML.evarKey b)).Nodup →
    (∀ b ∈ bs, ∃ n, b.sort = KoreAML.srt n) →
    (∀ e₁ : Valuation M, (∀ x, (∀ b ∈ bs, x ≠ tbl.ev (KoreAML.evarKey b)) → e₁.evalEvar x = e.evalEvar x) →
      (∀ b ∈ bs, ∀ n, b.sort = KoreAML.srt n → InS I n (e₁.evalEvar (tbl.ev (KoreAML.evarKey b)))) →
      CrossAt I τ τ' (KoreAML.tr ⟨tbl, []⟩ body) (KoreAML.tr ⟨tbl, []⟩ body') e₁) →
    CrossAt I τ τ' (KoreAML.tr ⟨tbl, []⟩ (KoreAML.existsAll S bs body))
      (KoreAML.tr ⟨tbl, []⟩ (KoreAML.existsAll S' bs body')) e
  | [], e, _, _, h => h e (fun _ _ => rfl) (fun _ hb => absurd hb List.not_mem_nil)
  | b :: bs, e, hnd, hs, h => by
    show CrossAt I τ τ' (KoreAML.tr ⟨tbl, []⟩ (.exist S b (KoreAML.existsAll S bs body)))
      (KoreAML.tr ⟨tbl, []⟩ (.exist S' b (KoreAML.existsAll S' bs body'))) e
    obtain ⟨n, hn⟩ := hs b (List.mem_cons_self ..)
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [tr_exist_resort, tr_exist_resort, hn, trSort_srt]
    refine crossAt_sExists hD (KoreAML.Closed.sym _) fun a ha => ?_
    refine crossAt_existsAll hD bs _ hnd.2 (fun b' hb' => hs b' (List.mem_cons_of_mem _ hb'))
      fun e₁ hoff hg => h e₁ (fun x hx => ?_) (fun b' hb' n' hn' => ?_)
    · rw [hoff x (fun b' hb' => hx b' (List.mem_cons_of_mem _ hb'))]
      exact Function.update_noteq (hx b (List.mem_cons_self ..)) _ _
    · rcases List.mem_cons.mp hb' with rfl | hb''
      · rw [hoff _ (fun b'' hb'' he => hnd.1 (List.mem_map.mpr ⟨b'', hb'', he.symm⟩))]
        show InS I n' (Function.update e.evalEvar _ a _)
        rw [Function.update_same, ← srt_inj (hn.symm.trans hn')]
        exact (inS_iff _).mp ha
      · exact hg b' hb'' n' hn'

end

/-! ## The variables of a condition's pattern at a sort without sort variables -/

/-- `existsAll` at a sort without sort variables holds no variable `existsAll` at another sort
over a body with more variables does not. -/
theorem varsOf_existsAll_resort {X Y : Kore.KSort} (hX : KoreAML.sortVarsOf X = []) {body body' : Kore.Pattern}
    (h : ∀ k ∈ KoreAML.varsOf body, k ∈ KoreAML.varsOf body') :
    ∀ (bs : List Kore.EVar), ∀ k ∈ KoreAML.varsOf (KoreAML.existsAll X bs body),
      k ∈ KoreAML.varsOf (KoreAML.existsAll Y bs body')
  | [] => h
  | b :: bs => by
    intro k hk
    change k ∈ KoreAML.varsOf (.exist X b (KoreAML.existsAll X bs body)) at hk
    show k ∈ KoreAML.varsOf (.exist Y b (KoreAML.existsAll Y bs body'))
    have ih := varsOf_existsAll_resort (Y := Y) hX h bs k
    simp only [KoreAML.varsOf, hX, List.nil_append, List.mem_append, or_assoc] at hk ⊢
    rcases hk with h1 | h1 | h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr (ih h1)))

/-- **A condition's pattern at a sort without sort variables holds no variable its pattern at
another sort does not**: the two differ in the sort arguments of the connectives. -/
theorem condKore_varsOf_resort {c : Semantics} {X Y : Kore.KSort} (hX : KoreAML.sortVarsOf X = []) :
    ∀ (p : Cond) (vs : List KoreAML.Var), ∀ k ∈ KoreAML.varsOf (Cond.kore c vs X p),
      k ∈ KoreAML.varsOf (Cond.kore c vs Y p)
  | .top, vs, k, hk => by
    simp only [Cond.kore, KoreAML.varsOf, hX] at hk
    cases hk
  | .bot, vs, k, hk => by
    simp only [Cond.kore, KoreAML.varsOf, hX] at hk
    cases hk
  | .not p, vs, k, hk => by
    have ih := condKore_varsOf_resort (c := c) (Y := Y) hX p vs k
    simp only [Cond.kore, KoreAML.varsOf, hX, List.nil_append, List.mem_append] at hk ⊢
    exact Or.inr (ih hk)
  | .and p q, vs, k, hk => by
    have ihp := condKore_varsOf_resort (c := c) (Y := Y) hX p vs k
    have ihq := condKore_varsOf_resort (c := c) (Y := Y) hX q vs k
    simp only [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList, hX, List.nil_append, List.append_nil,
      List.mem_append] at hk ⊢
    rcases hk with h1 | h1
    · exact Or.inr (Or.inl (ihp h1))
    · exact Or.inr (Or.inr (ihq h1))
  | .or p q, vs, k, hk => by
    have ihp := condKore_varsOf_resort (c := c) (Y := Y) hX p vs k
    have ihq := condKore_varsOf_resort (c := c) (Y := Y) hX q vs k
    simp only [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList, hX, List.nil_append, List.append_nil,
      List.mem_append] at hk ⊢
    rcases hk with h1 | h1
    · exact Or.inr (Or.inl (ihp h1))
    · exact Or.inr (Or.inr (ihq h1))
  | .implies p q, vs, k, hk => by
    have ihp := condKore_varsOf_resort (c := c) (Y := Y) hX p vs k
    have ihq := condKore_varsOf_resort (c := c) (Y := Y) hX q vs k
    simp only [Cond.kore, KoreAML.varsOf, hX, List.nil_append, List.mem_append, or_assoc] at hk ⊢
    rcases hk with h1 | h1
    · exact Or.inr (Or.inl (ihp h1))
    · exact Or.inr (Or.inr (ihq h1))
  | .ceil s t, vs, k, hk => by
    simp only [Cond.kore, KoreAML.varsOf, hX, List.append_nil, List.mem_append, or_assoc] at hk ⊢
    rcases hk with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr h1)
  | .equals s t u, vs, k, hk => by
    simp only [Cond.kore, KoreAML.varsOf, hX, List.append_nil, List.mem_append, or_assoc] at hk ⊢
    rcases hk with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr h1))
  | .mem s t u, vs, k, hk => by
    simp only [Cond.kore, KoreAML.varsOf, hX, List.append_nil, List.mem_append, or_assoc] at hk ⊢
    rcases hk with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr h1))
  | .exMatch ys s p t body, vs, k, hk => by
    rw [Cond.kore] at hk ⊢
    refine varsOf_existsAll_resort hX (fun k' hk' => ?_) _ k hk
    have ih := condKore_varsOf_resort (c := c) (Y := Y) hX body
      (vs ++ ((List.range ys.length).zip ys).map fun (j, y) => Cond.binder c (vs.length + j) y) k'
    simp only [KoreAML.varsOf, KoreAML.varsOfList, hX, List.nil_append, List.append_nil,
      List.mem_append, or_assoc] at hk' ⊢
    rcases hk' with h1 | h1 | h1 | h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ih h1)))))
  | .ex s body, vs, k, hk => by
    have ih := condKore_varsOf_resort (c := c) (Y := Y) hX body (vs ++ [Cond.binder c vs.length s]) k
    simp only [Cond.kore, KoreAML.varsOf, hX, List.nil_append, List.mem_append, or_assoc] at hk ⊢
    rcases hk with h1 | h1 | h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr (ih h1)))
  | .all s body, vs, k, hk => by
    have ih := condKore_varsOf_resort (c := c) (Y := Y) hX body (vs ++ [Cond.binder c vs.length s]) k
    simp only [Cond.kore, KoreAML.varsOf, hX, List.nil_append, List.mem_append, or_assoc] at hk ⊢
    rcases hk with h1 | h1 | h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr (ih h1)))

/-- A numbered sort's name holds no sort variable. -/
theorem sortVarsOf_srtOf (c : Semantics) (S : Srt) : KoreAML.sortVarsOf (srtOf c S) = [] := rfl

/-! ## A condition's pattern at `R` and at a numbered sort -/

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- The elements of a well-sorted term of a numbered sort, at a valuation of its variables in their
sorts, lie in its sort. -/
def TermsInSort (c : Semantics) {M : Type} [Inhabited M] (I : Interpretation KoreAML.Sym M) : Prop :=
  ∀ {vars : List Srt} {tbl : VarTable} {e : Valuation M} {t : Term} {s : Srt},
    sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t = some s → s < nRegSorts + c.sortNames.length →
    (∀ i ∈ varOccs t, InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (canonKey c vars i)))) →
    ∀ a, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c vars) t)).interpret I e a → InS I (c.sortName s) a

/-- Every model of `Γ c` has it (`rhsSort_at`). -/
theorem termsInSort_of_model (hI : I ⊧ᴵP Γ c) [OvlOK c] (hg : genWf c = true) : TermsInSort c I :=
  fun ht _ hin a ha => rhsSort_at hI hg fns_headsOK ht hin a ha

/-- Every model of `Γ c` of a definition `coreOK` accepts has it. -/
theorem termsInSort_of_core (h : c.coreOK = true) (hI : I ⊧ᴵP Γ c) : TermsInSort c I := by
  obtain ⟨-, -, -, hg, -, -, -, -, hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  intro vars tbl e t s ht hs hin a ha
  exact termsInSort_of_model hI hg ht hs hin a ha

omit [Inhabited M] in
/-- The sort variable `R` denotes the element the valuation gives it. -/
theorem sortR_den {tbl : VarTable} {e : Valuation M} {τR : M}
    (hR : e.evalEvar (tbl.ev (.sortVar "R")) = τR) (a : M) :
    (KoreAML.trSort tbl KoreAML.R).interpret I e a ↔ a = τR := by
  rw [trSort_R, KoreAML.interp_evar, hR]

omit [Inhabited M] in
/-- A valuation changed at a variable's key gives `R` what it gave. -/
theorem sortR_update {tbl : VarTable} {e : Valuation M} {x : Kore.EVar} (hx : KoreAML.evarKey x ∈ tbl)
    (hRm : VarKey.sortVar "R" ∈ tbl) (a : M) :
    Function.update e.evalEvar (tbl.ev (KoreAML.evarKey x)) a (tbl.ev (.sortVar "R")) =
      e.evalEvar (tbl.ev (.sortVar "R")) :=
  Function.update_noteq (fun he => by cases ev_inj hRm hx he) _ _

/-- **A condition's pattern at `R` holds where its pattern at a numbered sort does**, by
structural recursion on the condition: at a valuation that gives `R` a sort `τR` and each free
variable an element of its sort, through a table holding the keys of the pattern's variables, the
pattern at `R` holds at an element of `τR` iff the pattern at `srtOf c S` holds at an element of
the sort `τS` that `S` denotes. -/
theorem cond_crossAt (hD : DefOK I) (hc : I ⊧ᴵ KoreAML.ceilDefItem.pat)
    (hsort : ∀ {s : Srt}, s < nRegSorts + c.sortNames.length → ∃ τ, IsSort I τ ∧
      ∀ (tbl : VarTable) (e : Valuation M) (a : M), (KoreAML.trSort tbl (srtOf c s)).interpret I e a ↔ a = τ)
    (hT : TermsInSort c I) {S : Srt} {τS τR : M}
    (hτS : ∀ (tbl : VarTable) (e : Valuation M) (a : M), (KoreAML.trSort tbl (srtOf c S)).interpret I e a ↔ a = τS)
    (hσS : IsSort I τS) (hσR : IsSort I τR) :
    ∀ (p : Cond) {vars : List Srt} {tbl : VarTable} {e : Valuation M}, c.condOK vars p = true →
    (∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) KoreAML.R p), k ∈ tbl) →
    VarKey.sortVar "R" ∈ tbl →
    (∀ i ∈ varOccsCond vars.length p, canonKey c vars i ∈ tbl ∧
      InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (canonKey c vars i)))) →
    e.evalEvar (tbl.ev (.sortVar "R")) = τR →
    CrossAt I τR τS (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) KoreAML.R p))
      (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) (srtOf c S) p)) e
  | .top, vars, tbl, e, _, _, _, _, hR => crossAt_form (Q := True)
      (fun m => by
        rw [Cond.kore, tr_top_resort, KoreAML.interp_sTop hD isFree_R, KoreAML.interp_inhOf_of (sortR_den hR)]
        exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩)
      (fun m => by
        rw [Cond.kore, tr_top_resort, KoreAML.interp_sTop hD Model.srtOf_free_stdI,
          KoreAML.interp_inhOf_of (hτS tbl e)]
        exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩)
  | .bot, vars, tbl, e, _, _, _, _, hR => crossAt_form (Q := False)
      (fun m => by
        rw [Cond.kore, tr_bottom_resort]
        unfold KoreAML.sBot
        rw [KoreAML.interp_sNot, KoreAML.interp_sTop hD isFree_R]
        exact ⟨fun h => (h.1 h.2).elim, fun h => h.1.elim⟩)
      (fun m => by
        rw [Cond.kore, tr_bottom_resort]
        unfold KoreAML.sBot
        rw [KoreAML.interp_sNot, KoreAML.interp_sTop hD Model.srtOf_free_stdI]
        exact ⟨fun h => (h.1 h.2).elim, fun h => h.1.elim⟩)
  | .not p, vars, tbl, e, hok, hk, hRm, hf, hR => by
    rw [Semantics.condOK] at hok
    have ih := cond_crossAt hD hc hsort hT hτS hσS hσR p hok
      (fun k hk0 => hk k (by rw [Cond.kore, KoreAML.varsOf]; exact List.mem_append_right _ hk0)) hRm
      (fun i hi => hf i (by rw [varOccsCond]; exact hi)) hR
    simp only [Cond.kore, tr_not_resort]
    exact crossAt_sNot (sortR_den hR) (hτS tbl e) ih
  | .and p q, vars, tbl, e, hok, hk, hRm, hf, hR => by
    rw [Semantics.condOK, Bool.and_eq_true] at hok
    have ihp := cond_crossAt hD hc hsort hT hτS hσS hσR p hok.1 (fun k hk0 => hk k (by rw [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList]; exact List.mem_append_right _ (List.mem_append_left _ hk0))) hRm
      (fun i hi => hf i (by rw [varOccsCond]; exact List.mem_append_left _ hi)) hR
    have ihq := cond_crossAt hD hc hsort hT hτS hσS hσR q hok.2 (fun k hk0 => hk k (by rw [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList]; exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hk0)))) hRm
      (fun i hi => hf i (by rw [varOccsCond]; exact List.mem_append_right _ hi)) hR
    simp only [Cond.kore, tr_and2]
    exact crossAt_sAnd ihp ihq
  | .or p q, vars, tbl, e, hok, hk, hRm, hf, hR => by
    rw [Semantics.condOK, Bool.and_eq_true] at hok
    have ihp := cond_crossAt hD hc hsort hT hτS hσS hσR p hok.1 (fun k hk0 => hk k (by rw [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList]; exact List.mem_append_right _ (List.mem_append_left _ hk0))) hRm
      (fun i hi => hf i (by rw [varOccsCond]; exact List.mem_append_left _ hi)) hR
    have ihq := cond_crossAt hD hc hsort hT hτS hσS hσR q hok.2 (fun k hk0 => hk k (by rw [Cond.kore, KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList]; exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hk0)))) hRm
      (fun i hi => hf i (by rw [varOccsCond]; exact List.mem_append_right _ hi)) hR
    simp only [Cond.kore, Model.tr_or2Stdi]
    exact crossAt_sOr (sortR_den hR) (hτS tbl e) ihp ihq
  | .implies p q, vars, tbl, e, hok, hk, hRm, hf, hR => by
    rw [Semantics.condOK, Bool.and_eq_true] at hok
    have ihp := cond_crossAt hD hc hsort hT hτS hσS hσR p hok.1 (fun k hk0 => hk k (by rw [Cond.kore, KoreAML.varsOf]; exact List.mem_append_left _ (List.mem_append_right _ hk0))) hRm
      (fun i hi => hf i (by rw [varOccsCond]; exact List.mem_append_left _ hi)) hR
    have ihq := cond_crossAt hD hc hsort hT hτS hσS hσR q hok.2 (fun k hk0 => hk k (by rw [Cond.kore, KoreAML.varsOf]; exact List.mem_append_right _ hk0)) hRm
      (fun i hi => hf i (by rw [varOccsCond]; exact List.mem_append_right _ hi)) hR
    simp only [Cond.kore, tr_implies_resort]
    exact crossAt_sImp (sortR_den hR) (hτS tbl e) ihp ihq
  | .ceil s t, vars, tbl, e, hok, _, _, hf, hR => by
    simp only [Semantics.condOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨ht, hs⟩ := hok
    obtain ⟨τ, hσ, hτ⟩ := hsort hs
    have hin : ∀ a, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c vars) t)).interpret I e a → Inh I τ a :=
      fun a ha => (KoreAML.interp_inhOf_of (hτ tbl e)).mp (HoldsShape.inhOf_srtOf_inS.mpr
        (hT ht hs (fun i hi => (hf i (by rw [varOccsCond]; exact hi)).2) a ha))
    simp only [Cond.kore, tr_ceil_resort]
    exact crossAt_form
      (fun m => KoreAML.interp_sCeil hD hc (hτ tbl e) (sortR_den hR) hσ hσR hin m)
      (fun m => KoreAML.interp_sCeil hD hc (hτ tbl e) (hτS tbl e) hσ hσS hin m)
  | .equals s t u, vars, tbl, e, hok, _, _, _, hR => by
    simp only [Semantics.condOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨-, hs⟩ := hok
    obtain ⟨τ, hσ, hτ⟩ := hsort hs
    simp only [Cond.kore, tr_equals_resort]
    exact crossAt_form
      (fun m => (KoreAML.interp_sEquals hD hc (hτ tbl e) (sortR_den hR) hσ hσR m).trans and_comm)
      (fun m => (KoreAML.interp_sEquals hD hc (hτ tbl e) (hτS tbl e) hσ hσS m).trans and_comm)
  | .mem s t u, vars, tbl, e, hok, _, _, hf, hR => by
    simp only [Semantics.condOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨⟨ht, -⟩, hs⟩ := hok
    obtain ⟨τ, hσ, hτ⟩ := hsort hs
    have hin : ∀ a, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c vars) t)).interpret I e a → Inh I τ a :=
      fun a ha => (KoreAML.interp_inhOf_of (hτ tbl e)).mp (HoldsShape.inhOf_srtOf_inS.mpr
        (hT ht hs (fun i hi => (hf i (by rw [varOccsCond]; exact List.mem_append_left _ hi)).2) a ha))
    simp only [Cond.kore, tr_in_resort]
    exact crossAt_form
      (fun m => KoreAML.interp_sIn hD hc (hτ tbl e) (sortR_den hR) hσ hσR hin m)
      (fun m => KoreAML.interp_sIn hD hc (hτ tbl e) (hτS tbl e) hσ hσS hin m)
  | .exMatch ys s p t body, vars, tbl, e, hok, hk, hRm, hf, hR => by
    have hok0 := hok
    simp only [Semantics.condOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hpS, htS⟩, hbody⟩, hsN⟩ := hok
    obtain ⟨τ, hσ, hτ⟩ := hsort hsN
    have hkore : ∀ X : Kore.KSort, Cond.kore c (canonVars c vars) X (.exMatch ys s p t body) =
        KoreAML.existsAll X
          ((List.range' vars.length ys.length).map fun i => ((canonVars c (vars ++ ys)).getD i default).kore)
          (.and X
            [.in (srtOf c s) X (Term.kore c (canonVars c vars) t) (Term.kore c (canonVars c (vars ++ ys)) p),
             Cond.kore c (canonVars c (vars ++ ys)) X body]) := by
      intro X
      rw [← Model.binders_eqStdI (c := c) vars ys, ← Model.canonVars_appendStdI c vars ys]; rfl
    rw [hkore] at hk
    rw [hkore, hkore]
    have hl : ∀ i ∈ List.range' vars.length ys.length, vars.length ≤ i ∧ i < (vars ++ ys).length :=
      fun i hi => by
        have := List.mem_range'_1.mp hi
        simp only [List.length_append]; omega
    have hkB : ∀ i ∈ List.range' vars.length ys.length, canonKey c (vars ++ ys) i ∈ tbl := fun i hi =>
      hk _ (varsOf_existsAll_binder _ (List.mem_map_of_mem (f := fun i => ((canonVars c (vars ++ ys)).getD i default).kore) hi))
    have hnd : (((List.range' vars.length ys.length).map fun i => ((canonVars c (vars ++ ys)).getD i default).kore).map
        fun b => tbl.ev (KoreAML.evarKey b)).Nodup := by
      rw [List.map_map]
      refine List.pairwise_map.mpr ((List.nodup_range' (s := vars.length) (n := ys.length)).imp_of_mem fun {i j} hi hj hne he => hne ?_)
      exact canonKey_inj (hl i hi).2 (hl j hj).2 (ev_inj (hkB i hi) (hkB j hj) he)
    have hsrt := binders_sortEx (c := c) (vars := vars ++ ys) (l := List.range' vars.length ys.length)
      fun i hi => (hl i hi).2
    -- off the binders, the outer free variables keep their elements
    have hout : ∀ i ∈ varOccsCond vars.length (.exMatch ys s p t body), ∀ e₁ : Valuation M,
        (∀ x, (∀ b ∈ (List.range' vars.length ys.length).map fun i => ((canonVars c (vars ++ ys)).getD i default).kore,
          x ≠ tbl.ev (KoreAML.evarKey b)) → e₁.evalEvar x = e.evalEvar x) →
        e₁.evalEvar (tbl.ev (canonKey c vars i)) = e.evalEvar (tbl.ev (canonKey c vars i)) := by
      intro i hi e₁ hoff
      refine hoff _ fun b hb he => ?_
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
      have hlt := varOccsCond_lt_twoT (.exMatch ys s p t body) hok0 i hi
      have := canonKey_inj (c := c) (vars := vars ++ ys) (i := i) (j := j) (by simp only [List.length_append]; omega)
        (hl j hj).2 ((Model.canonKey_appendStdI hlt).trans (ev_inj (hf i hi).1 (hkB j hj) he))
      have := (hl j hj).1
      omega
    -- and `R` keeps its sort
    have hRout : ∀ e₁ : Valuation M,
        (∀ x, (∀ b ∈ (List.range' vars.length ys.length).map fun i => ((canonVars c (vars ++ ys)).getD i default).kore,
          x ≠ tbl.ev (KoreAML.evarKey b)) → e₁.evalEvar x = e.evalEvar x) →
        e₁.evalEvar (tbl.ev (.sortVar "R")) = τR := by
      intro e₁ hoff
      rw [hoff _ fun b hb he => ?_]
      · exact hR
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
        cases ev_inj hRm (hkB j hj) he
    refine crossAt_existsAll hD _ e hnd hsrt fun e₁ hoff hguard => ?_
    have hR₁ := hRout e₁ hoff
    rw [tr_and2, tr_and2]
    refine crossAt_sAnd ?_ ?_
    · have hin : ∀ a, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c vars) t)).interpret I e₁ a → Inh I τ a :=
        fun a ha => (KoreAML.interp_inhOf_of (hτ tbl e₁)).mp (HoldsShape.inhOf_srtOf_inS.mpr
          (hT htS hsN (fun i hi => by
            have hiO : i ∈ varOccsCond vars.length (.exMatch ys s p t body) := by
              rw [varOccsCond]; exact List.mem_append_left _ hi
            rw [hout i hiO e₁ hoff]; exact (hf i hiO).2) a ha))
      rw [tr_in_resort, tr_in_resort]
      exact crossAt_form
        (fun m => KoreAML.interp_sIn hD hc (hτ tbl e₁) (sortR_den hR₁) hσ hσR hin m)
        (fun m => KoreAML.interp_sIn hD hc (hτ tbl e₁) (hτS tbl e₁) hσ hσS hin m)
    · refine cond_crossAt hD hc hsort hT hτS hσS hσR body hbody (fun k hk0 => hk k (HoldsShape.varsOf_existsAll_bodyHF
        (Model.varsOf_and_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _)) hk0) _)) hRm (fun i hi => ?_) hR₁
      have hlt := varOccsCond_lt_twoT body hbody i hi
      have hlen : (vars ++ ys).length = vars.length + ys.length := by simp
      rw [hlen] at hlt hi
      by_cases hin : i < vars.length
      · have hiO : i ∈ varOccsCond vars.length (.exMatch ys s p t body) := by
          rw [varOccsCond]
          exact List.mem_append_right _ (List.mem_filter.mpr ⟨List.mem_append_right _ hi, by simpa using hin⟩)
        rw [Model.canonKey_appendStdI hin, Model.getD_appendL_stdI _ _ _ hin, hout i hiO e₁ hoff]
        exact hf i hiO
      · have hil : i ∈ List.range' vars.length ys.length := List.mem_range'_1.mpr ⟨by omega, by omega⟩
        refine ⟨hkB i hil, hguard _ (List.mem_map_of_mem (f := fun i => ((canonVars c (vars ++ ys)).getD i default).kore) hil) _ ?_⟩
        show ((canonVars c (vars ++ ys)).getD i default).kore.sort = _
        rw [canonVars_getD c (show i < (vars ++ ys).length by rw [hlen]; exact hlt)]; rfl
  | .ex s body, vars, tbl, e, hok, hk, hRm, hf, hR => by
    rw [Semantics.condOK] at hok
    have hkore : ∀ X : Kore.KSort, Cond.kore c (canonVars c vars) X (.ex s body) =
        .exist X (Cond.binder c (canonVars c vars).length s).kore
          (Cond.kore c (canonVars c (vars ++ [s])) X body) := by
      intro X
      rw [← Model.canonVars_snocStdI c vars s]; rfl
    rw [hkore] at hk
    have hkb := Model.binder_keyStdI (c := c) vars s
    have hK := hk (canonKey c (vars ++ [s]) vars.length) (by rw [KoreAML.varsOf, hkb]; simp)
    have hKb : KoreAML.evarKey (Cond.binder c (canonVars c vars).length s).kore ∈ tbl := by rw [hkb]; exact hK
    have hbs : (Cond.binder c (canonVars c vars).length s).kore.sort = srtOf c s := rfl
    rw [hkore, hkore, tr_exist_resort, tr_exist_resort, hbs, trSort_srtOf_twoT]
    refine crossAt_sExists hD (KoreAML.Closed.sym _) fun a ha => ?_
    have hR' := (sortR_update (e := e) hKb hRm a).trans hR
    have hbody := cond_crossAt hD hc hsort hT hτS hσS hσR body hok
      (fun k hk0 => hk k (by rw [KoreAML.varsOf]; exact List.mem_append_right _ hk0)) hRm
      (binder_inS hok hK (fun i hi hl => hf i (by rw [varOccsCond]; exact List.mem_filter.mpr ⟨hi, by simpa using hl⟩))
        ((inS_iff e).mp ha))
      (e := ⟨Function.update e.evalEvar (tbl.ev (canonKey c (vars ++ [s]) vars.length)) a, e.evalSvar⟩)
      (by rw [← hkb]; exact hR')
    rw [hkb]
    exact hbody
  | .all s body, vars, tbl, e, hok, hk, hRm, hf, hR => by
    rw [Semantics.condOK] at hok
    have hkore : ∀ X : Kore.KSort, Cond.kore c (canonVars c vars) X (.all s body) =
        .forall X (Cond.binder c (canonVars c vars).length s).kore
          (Cond.kore c (canonVars c (vars ++ [s])) X body) := by
      intro X
      rw [← Model.canonVars_snocStdI c vars s]; rfl
    rw [hkore] at hk
    have hkb := Model.binder_keyStdI (c := c) vars s
    have hK := hk (canonKey c (vars ++ [s]) vars.length) (by rw [KoreAML.varsOf, hkb]; simp)
    have hKb : KoreAML.evarKey (Cond.binder c (canonVars c vars).length s).kore ∈ tbl := by rw [hkb]; exact hK
    have hbs : (Cond.binder c (canonVars c vars).length s).kore.sort = srtOf c s := rfl
    rw [hkore, hkore, tr_forall_resort, tr_forall_resort, hbs]
    unfold KoreAML.sForall
    refine crossAt_sNot (sortR_den hR) (hτS tbl e) ?_
    rw [trSort_srtOf_twoT]
    refine crossAt_sExists hD (KoreAML.Closed.sym _) fun a ha => ?_
    have hR' := (sortR_update (e := e) hKb hRm a).trans hR
    have hbody := cond_crossAt hD hc hsort hT hτS hσS hσR body hok
      (fun k hk0 => hk k (by rw [KoreAML.varsOf]; exact List.mem_append_right _ hk0)) hRm
      (binder_inS hok hK (fun i hi hl => hf i (by rw [varOccsCond]; exact List.mem_filter.mpr ⟨hi, by simpa using hl⟩))
        ((inS_iff e).mp ha))
      (e := ⟨Function.update e.evalEvar (tbl.ev (canonKey c (vars ++ [s]) vars.length)) a, e.evalSvar⟩)
      (by rw [← hkb]; exact hR')
    rw [hkb]
    exact crossAt_sNot (sortR_den (by rw [← hkb]; exact hR')) (hτS tbl _) hbody

end

end Faithful

open ML Faithful

namespace HoldsShape

section
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The Holds lemma at the sort variable `R`**: for a condition with the Holds lemma in I
(`HoldsDenB` over a Bool that bounds its binders, at a numbered sort), in an interpretation with the atoms' facts where a well-sorted
term's elements lie in its sort, at a valuation that reads the condition's free variables as their
values under σ and gives `R` a sort `σr`, through a table holding `R` and the variables of the
pattern at `R`: an element of `σr` is in `Cond.kore … R p` exactly where the truth value `Holds`
gives is `true`. -/
theorem holds_atR (F : AtomFacts c I) (hT : TermsInSort c I) {bd : Nat → Cond → Bool} {p : Cond}
    (hp : HoldsDenB bd c I p)
    {vars : List Srt} {P : Nat → Prop} {σ : Subst} {b : Bool} {tbl : KoreAML.VarTable} {e : Valuation M}
    (hok : c.condOK vars p = true) (hbd : bd vars.length p = true)
    (hP : ∀ i ∈ varOccsCond vars.length p, i < vars.length → P i) (hr : Reads c I vars P σ tbl e)
    (hk : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c vars) KoreAML.R p), k ∈ tbl)
    (hRm : KoreAML.VarKey.sortVar "R" ∈ tbl) {σr : M}
    (hR : ∀ a, (KoreAML.trSort tbl KoreAML.R).interpret I e a ↔ a = σr) (hσr : KoreAML.IsSort I σr)
    (hh : Holds c vars.length σ p b) (a : M) (ha : KoreAML.Inh I σr a) :
    (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) KoreAML.R p)).interpret I e a ↔ b = true := by
  have hS : Srt.bool < nRegSorts + c.sortNames.length := F.valNum (sortOf_bool (c := c) true)
  obtain ⟨a0, -, ha0⟩ := F.val (sortOf_bool (c := c) true) tbl e
  obtain ⟨τS, hσS, hτS⟩ := F.sort hS
  have hRe : e.evalEvar (tbl.ev (.sortVar "R")) = σr :=
    ((hR _).mp (by rw [trSort_R, KoreAML.interp_evar])).symm ▸ rfl
  have hf : ∀ i ∈ varOccsCond vars.length p, canonKey c vars i ∈ tbl ∧
      InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (canonKey c vars i))) := fun i hi => by
    have hPi := hP i hi (varOccsCond_lt_twoT p hok i hi)
    exact ⟨(hr i hPi).2.1, inhOf_srtOf_inS.mp (hr.inSort F hPi)⟩
  rw [cond_crossAt F.defOK F.ceilDef F.sort hT hτS hσS hσr p hok hk hRm hf hRe a a0 ha
    ((KoreAML.interp_inhOf_of (hτS tbl e)).mp ha0)]
  exact hp hok hbd hP hr (fun k hk0 => hk k (condKore_varsOf_resort (sortVarsOf_srtOf c Srt.bool) p _ k hk0))
    hS hh a0 ha0

end

end HoldsShape

end KCore
