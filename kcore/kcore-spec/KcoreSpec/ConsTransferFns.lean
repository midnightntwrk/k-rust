/-
  The extension of a model of the theory without the detached names (`extModel`,
  ConsExtModel.lean) satisfies the premises of the functions that name nothing of `D`
  (`sat_own_fns`), and with them every premise of the functions, the rules, the step's closure,
  the domains, the interpretation's values at silent points and the closure axiom of Bool
  (`sat_own_fns_rules`).

  A function's equation is a sentence `axiom{R} \implies{R}(premise, \equals{S,R}(f(X̄), rhs ∧ ens))`
  at its sort variable, with `∃ē. (rhs ∧ ens ∧ post)` beside `\top` on the right where the clause
  has existential variables (`clauseRhs`). For a clause whose predicate is `\top` its pattern is of
  the class `RFrag`: `\top`, `\bottom`, negation, conjunction,
  disjunction and implication at `R`, an equality `\equals{S,R}` and a membership `\in{S,R}` of a
  variable, both between patterns at sort constants (`KFrag`, ConsTransferFrag.lean), and a
  quantifier `\exists{R}` at a sort constant, which a competitor's exclusion writes; the right
  side's binders and predicate are at the result sort, inside `KFrag`. The
  translation of such a pattern is of the class `RPred` (`rpred_rfrag_fn`), so
  `transfer_trAxiom_R` (ConsTransferR.lean) carries the equation.
-/
import KcoreSpec.ConsTransferFrag

set_option autoImplicit false

namespace KCore.Cons

open ML Faithful
open KoreAML (DefOK Inh IsSort VarKey VarTable)

local notation "Own0" => OwnSorted (fun _ => False)

/-- **The patterns at the sort variable `R`** of a function's equation; `S` names the sort
constants an equality, a membership or a quantifier may be at. -/
inductive RFrag (S : String → Prop) : Kore.Pattern → Prop
  | top : RFrag S (.top KoreAML.R)
  | bottom : RFrag S (.bottom KoreAML.R)
  | not {p : Kore.Pattern} : RFrag S p → RFrag S (.not KoreAML.R p)
  | and {p q : Kore.Pattern} : RFrag S p → RFrag S q → RFrag S (.and KoreAML.R [p, q])
  | or {p q : Kore.Pattern} : RFrag S p → RFrag S q → RFrag S (.or KoreAML.R [p, q])
  | implies {p q : Kore.Pattern} : RFrag S p → RFrag S q → RFrag S (.implies KoreAML.R p q)
  | equals {C : Kore.SortIdent} {p q : Kore.Pattern} : S C.ident.name → KFrag p → KFrag q →
      RFrag S (.equals (.ctor C []) KoreAML.R p q)
  | inn {C : Kore.SortIdent} {x : Kore.EVar} {q : Kore.Pattern} : S C.ident.name → x.sort = .ctor C [] →
      KFrag q → RFrag S (.in (.ctor C []) KoreAML.R (.var (.evar x)) q)
  | exist {C : Kore.SortIdent} {x : Kore.EVar} {p : Kore.Pattern} : S C.ident.name → x.sort = .ctor C [] →
      RFrag S p → RFrag S (.exist KoreAML.R x p)

/-- Two keys with one index in a table that holds one of them are one key. -/
theorem ev_inj_fn {t : VarTable} {k k' : VarKey} (hk : k ∈ t) (h : t.ev k = t.ev k') : k = k' := by
  have h' : t.idxOf k = t.idxOf k' := by
    simpa only [VarTable.ev, VarTable.index, EVar.mk.injEq, Nat.add_right_cancel_iff] using h
  have hk' : k' ∈ t := List.idxOf_lt_length_iff.mp (h' ▸ List.idxOf_lt_length_of_mem hk)
  exact Faithful.ev_inj hk hk' h

/-- The key of a variable of a sort constant names that sort. -/
theorem keySortName_evarKey_fn {x : Kore.EVar} {C : Kore.SortIdent} (hx : x.sort = .ctor C []) :
    keySortName (KoreAML.evarKey x) = C.ident.name := by
  unfold KoreAML.evarKey; rw [hx]; rfl

/-- **The translation of a pattern at the sort variable is of the class `RPred`**, at the names of
no symbol, with `G` holding the indices of the bound keys `B` and of the free keys, each beside
the name of its sort. -/
theorem rpred_rfrag_fn {S : String → Prop} (t : VarTable) (hRt : VarKey.sortVar "R" ∈ t) {p : Kore.Pattern}
    (hp : RFrag S p) :
    ∀ (B : List VarKey) (G : List (EVar × String)), (∀ k ∈ KoreAML.varsOf p, k ∈ t) →
      (∀ k ∈ B, (t.ev k, keySortName k) ∈ G) → (∀ k ∈ KoreAML.freeOf B p, (t.ev k, keySortName k) ∈ G) →
      RPred (fun _ => False) S (t.ev (.sortVar "R")) G (KoreAML.tr ⟨t, []⟩ p) := by
  have hO : ∀ N, S N → ¬ (fun _ : KoreAML.Sym => False) (.sort N) := fun _ _ h => h
  have hV : ∀ {B : List VarKey} {G : List (EVar × String)} {q : Kore.Pattern},
      (∀ k ∈ B, (t.ev k, keySortName k) ∈ G) → (∀ k ∈ KoreAML.freeOf B q, (t.ev k, keySortName k) ∈ G) →
      KFrag q → Own0 (G.map (·.1)) [] .old (KoreAML.tr ⟨t, []⟩ q) := fun {B G q} hB hf hq =>
    (own_kfrag_fg t hq B _ (fun k hk => List.mem_map.mpr ⟨_, hB k hk, rfl⟩)
      (fun k hk => List.mem_map.mpr ⟨_, hf k hk, rfl⟩)).toOld
  induction hp with
  | top => intro B G _ _ _; rw [KoreAML.tr, trSort_R]; exact .top
  | bottom => intro B G _ _ _; rw [KoreAML.tr, trSort_R]; exact .sBot
  | not _ ih =>
    intro B G hv hB hf
    rw [KoreAML.tr, trSort_R]
    rw [KoreAML.varsOf] at hv
    rw [KoreAML.freeOf] at hf
    exact .not (ih B G (fun k hk => hv k (List.mem_append_right _ hk)) hB hf)
  | @and p q _ _ ih1 ih2 =>
    intro B G hv hB hf
    have htr : KoreAML.tr ⟨t, []⟩ (.and KoreAML.R [p, q]) =
        KoreAML.sAnd (KoreAML.tr ⟨t, []⟩ p) (KoreAML.tr ⟨t, []⟩ q) := by
      rw [KoreAML.tr, KoreAML.trAndList, KoreAML.trAndList]
    rw [htr]
    rw [KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList, KoreAML.varsOfList] at hv
    rw [KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOfList] at hf
    exact .and (ih1 B G (fun k hk => hv k (by simp [hk])) hB (fun k hk => hf k (by simp [hk])))
      (ih2 B G (fun k hk => hv k (by simp [hk])) hB (fun k hk => hf k (by simp [hk])))
  | @or p q _ _ ih1 ih2 =>
    intro B G hv hB hf
    have htr : KoreAML.tr ⟨t, []⟩ (.or KoreAML.R [p, q]) =
        KoreAML.sOr (.evar (t.ev (.sortVar "R"))) (KoreAML.tr ⟨t, []⟩ p) (KoreAML.tr ⟨t, []⟩ q) := by
      rw [KoreAML.tr, KoreAML.trOrList, KoreAML.trOrList, trSort_R]
    rw [htr]
    rw [KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList, KoreAML.varsOfList] at hv
    rw [KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOfList] at hf
    exact .sOr (ih1 B G (fun k hk => hv k (by simp [hk])) hB (fun k hk => hf k (by simp [hk])))
      (ih2 B G (fun k hk => hv k (by simp [hk])) hB (fun k hk => hf k (by simp [hk])))
  | implies _ _ ih1 ih2 =>
    intro B G hv hB hf
    rw [KoreAML.tr, trSort_R]
    rw [KoreAML.varsOf] at hv
    rw [KoreAML.freeOf] at hf
    exact .sImp (ih1 B G (fun k hk => hv k (by simp [hk])) hB (fun k hk => hf k (by simp [hk])))
      (ih2 B G (fun k hk => hv k (by simp [hk])) hB (fun k hk => hf k (by simp [hk])))
  | equals hN hp hq =>
    intro B G _ hB hf
    rw [KoreAML.tr, trSort_R, KoreAML.trSort_const]
    rw [KoreAML.freeOf] at hf
    exact .sEquals hO hN (hV hB (fun k hk => hf k (by simp [hk])) hp)
      (hV hB (fun k hk => hf k (by simp [hk])) hq)
  | @inn C x q hN hx hq =>
    intro B G _ hB hf
    rw [KoreAML.tr, trSort_R, KoreAML.trSort_const, KoreAML.tr]
    rw [KoreAML.freeOf, KoreAML.freeOf] at hf
    refine .sIn hN ?_ (hV hB (fun k hk => hf k (by simp [hk])) hq)
    rw [← keySortName_evarKey_fn hx]
    by_cases hc : B.contains (KoreAML.evarKey x) = true
    · exact hB _ (List.contains_iff_mem.mp hc)
    · exact hf _ (List.mem_append_left _ (by simp only [hc, Bool.false_eq_true, ↓reduceIte, List.mem_singleton]))
  | @exist C x p hN hx _ ih =>
    intro B G hv hB hf
    rw [KoreAML.tr, hx, KoreAML.trSort_const]
    rw [KoreAML.varsOf] at hv
    rw [KoreAML.freeOf] at hf
    have hxt : KoreAML.evarKey x ∈ t := hv _ (by simp)
    have hne : ∀ k, k ≠ KoreAML.evarKey x → t.ev k ≠ t.ev (KoreAML.evarKey x) := fun k hk h =>
      hk (ev_inj_fn hxt h.symm).symm
    have hin : ∀ k, (t.ev k, keySortName k) ∈ G →
        (t.ev k, keySortName k) ∈ (t.ev (KoreAML.evarKey x), C.ident.name) ::
          G.filter (fun q => decide (q.1 ≠ t.ev (KoreAML.evarKey x))) := fun k hk => by
      by_cases hkx : k = KoreAML.evarKey x
      · subst hkx; rw [keySortName_evarKey_fn hx]; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hk, decide_eq_true (hne k hkx)⟩)
    refine .ex hN (fun h => ?_) (ih (KoreAML.evarKey x :: B) _ (fun k hk => hv k (by simp [hk])) ?_ ?_)
    · have := ev_inj_fn hRt h.symm
      cases this
    · intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · rw [keySortName_evarKey_fn hx]; exact List.mem_cons_self ..
      · exact hin k (hB k hk)
    · intro k hk
      by_cases hkB : k ∈ KoreAML.evarKey x :: B
      · rcases List.mem_cons.mp hkB with rfl | hkB
        · rw [keySortName_evarKey_fn hx]; exact List.mem_cons_self ..
        · exact hin k (hB k hkB)
      · exact hin k (hf k hk)

/-- `D` reaches a pattern of the class `RPred` only through its symbols: a pattern of the class at
any set of names, none of whose symbols is in `D`, is of the class at `D`, and each sort it is at
is outside `D`. -/
theorem rpred_clean_fn {D D' : KoreAML.Sym → Prop} {O : String → Prop} {R : EVar}
    {G : List (EVar × String)} {π : KoreAML.P} (h : RPred D' O R G π) :
    (∀ σ ∈ psyms π, ¬ D σ) → RPred D (fun N => O N ∧ ¬ D (.sort N)) R G π := by
  induction h with
  | ceil hN hψ hw =>
    intro hn
    exact .ceil ⟨hN, hn _ (by simp [psyms, KoreAML.sCeil, KoreAML.sym])⟩
      (ownSorted_clean_sg hψ fun σ hσ => hn σ (by simp [psyms, KoreAML.sCeil, hσ])) hw
  | top => intro _; exact .top
  | not _ ih =>
    intro hn
    exact .not (ih fun σ hσ => hn σ (by
      simp [psyms, KoreAML.sNot, Pattern.conjunction, Pattern.disjunction, Pattern.negation, hσ]))
  | and _ _ ih1 ih2 =>
    intro hn
    exact .and
      (ih1 fun σ hσ => hn σ (by
        simp [psyms, KoreAML.sAnd, Pattern.conjunction, Pattern.disjunction, Pattern.negation, hσ]))
      (ih2 fun σ hσ => hn σ (by
        simp [psyms, KoreAML.sAnd, Pattern.conjunction, Pattern.disjunction, Pattern.negation, hσ]))
  | ex hN hx _ ih =>
    intro hn
    exact .ex ⟨hN, hn _ (by
        simp [psyms, KoreAML.sExists, ML.member, KoreAML.inhOf, KoreAML.sym, Pattern.conjunction,
          Pattern.disjunction, Pattern.negation])⟩ hx
      (ih fun σ hσ => hn σ (by
        simp [psyms, KoreAML.sExists, Pattern.conjunction, Pattern.disjunction, Pattern.negation, hσ]))

/-! ## The equations' patterns are of the class -/

section
variable {S : String → Prop}

theorem rfrag_reqPat_fn (hB : S ("Sort" ++ "Bool")) : ∀ (r : Option Kore.Pattern), (∀ p, r = some p → KFrag p) →
    RFrag S (reqPat KoreAML.R r)
  | none, _ => by rw [reqPat]; exact .top
  | some p, h => by rw [reqPat]; exact .equals hB (h p rfl) .dv

theorem rfrag_argsConj_fn : ∀ (l : List (String × Kore.Pattern)) (i : Nat),
    (∀ sp ∈ l, S ("Sort" ++ sp.1) ∧ KFrag sp.2) → RFrag S (KoreAML.argsConj i l)
  | [], _, _ => by rw [KoreAML.argsConj]; exact .top
  | (s, p) :: l, i, h => by
    rw [KoreAML.argsConj]
    exact .and (.inn (h _ (List.mem_cons_self ..)).1 rfl (h _ (List.mem_cons_self ..)).2)
      (rfrag_argsConj_fn l (i + 1) fun sp hsp => h sp (List.mem_cons_of_mem _ hsp))

/-- The premise of a clause whose predicate is `\top`: `⌈req = true⌉ ∧ X̄ ∈ p̄`. -/
theorem rfrag_premise_fn (hB : S ("Sort" ++ "Bool")) {args : List String} {req : Option Kore.Pattern}
    {pats : List Kore.Pattern} (ha : ∀ s ∈ args, S ("Sort" ++ s)) (hr : ∀ p, req = some p → KFrag p)
    (hp : ∀ p ∈ pats, KFrag p) : RFrag S (premise args req pats) := by
  unfold premise
  exact .and (rfrag_reqPat_fn hB req hr) (rfrag_argsConj_fn _ 0 fun sp hsp =>
    ⟨ha _ (List.of_mem_zip hsp).1, hp _ (List.of_mem_zip hsp).2⟩)

theorem rfrag_existsAll_fn {body : Kore.Pattern} (hb : RFrag S body) : ∀ (bs : List Kore.EVar),
    (∀ b ∈ bs, ∃ C, b.sort = .ctor C [] ∧ S C.ident.name) → RFrag S (KoreAML.existsAll KoreAML.R bs body)
  | [], _ => hb
  | b :: bs, h => by
    obtain ⟨C, hC, hS⟩ := h b (List.mem_cons_self ..)
    exact .exist hS hC (rfrag_existsAll_fn hb bs fun b' h' => h b' (List.mem_cons_of_mem _ h'))

theorem rfrag_anyOf_fn : ∀ (es : List Kore.Pattern), (∀ e ∈ es, RFrag S e) → RFrag S (KoreAML.anyOf es)
  | [], _ => by rw [KoreAML.anyOf]; exact .bottom
  | e :: es, h => by
    rw [KoreAML.anyOf]
    exact .or (h e (List.mem_cons_self ..)) (rfrag_anyOf_fn es fun e' h' => h e' (List.mem_cons_of_mem _ h'))

end

theorem withPres_fst_fn {α β : Type} [Inhabited β] : ∀ (as : List α) (bs : List β),
    ∀ p ∈ KoreAML.withPres as bs, p.1 ∈ as
  | [], _, p, hp => by rw [KoreAML.withPres] at hp; exact absurd hp List.not_mem_nil
  | a :: as, bs, p, hp => by
    rw [KoreAML.withPres] at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (withPres_fst_fn as bs.tail p hp)

/-- A variable of a clause or rule has one of the sorts given. -/
theorem varList_sort_fn {sorts names : List String} {v : KoreAML.Var} (hv : v ∈ KoreAML.varList sorts names) :
    v.sort ∈ sorts := by
  unfold KoreAML.varList at hv
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
  exact withPres_fst_fn _ _ p hp

theorem kfrag_numbered_fn (pre : String) : ∀ (ss : List String) (i : Nat),
    ∀ p ∈ KoreAML.vars (KoreAML.numbered pre i ss), KFrag p
  | [], _, p, hp => by
    rw [KoreAML.numbered] at hp; exact absurd hp List.not_mem_nil
  | s :: ss, i, p, hp => by
    rw [KoreAML.numbered] at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact .var ⟨_, rfl⟩
    · exact kfrag_numbered_fn pre ss (i + 1) p hp

section
variable {c : Semantics} {S : String → Prop}

/-- The exclusion of a clause whose predicate is `\top`: `∃ȳ. ⌈req = true⌉ ∧ X̄ ∈ p̄`. -/
theorem rfrag_exclusion_fn (hB : S ("Sort" ++ "Bool")) (f : Fn) (cl : Clause) (cp : ClausePres)
    (ha : ∀ s ∈ f.args, S ("Sort" ++ c.sortName s)) (hv : ∀ s ∈ cl.vars, S ("Sort" ++ c.sortName s))
    (hpre : cl.pre = .top) : RFrag S (exclusion c f cl cp) := by
  unfold exclusion
  simp only [withPre_top hpre]
  refine rfrag_existsAll_fn (rfrag_premise_fn hB (fun s hs => ?_) (fun p hp => ?_) (kfrag_koreList_fg c _ _)) _
    fun b hb => ?_
  · obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
    exact ha s' hs'
  · obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp hp
    exact kfrag_kore_fg c _ t
  · obtain ⟨v, hv', rfl⟩ := List.mem_map.mp hb
    obtain ⟨i, -, hi⟩ := List.mem_filterMap.mp hv'
    obtain ⟨s', hs', hs⟩ := List.mem_map.mp (varList_sort_fn (List.mem_of_getElem? hi))
    exact ⟨_, rfl, hs ▸ hv s' hs'⟩

/-- Existential binders over a pattern of the fragment, each at a variable of a sort constant. -/
theorem kfrag_foldrExist_fn (S : Kore.KSort) {body : Kore.Pattern} (hb : KFrag body) :
    ∀ L : List KoreAML.Var, KFrag (L.foldr (fun v p => Kore.Pattern.exist S v.kore p) body)
  | [] => hb
  | v :: L => .exist (varKore_sort_fg v) (kfrag_foldrExist_fn S hb L)

/-- Both parts of a clause's right side are of the fragment: `rhs` and `ens` where the clause has
no existential variable, and `∃ē. (rhs ∧ ens ∧ post)` beside `\top` where it has some. -/
theorem kfrag_clauseRhs_fn (c : Semantics) (f : Fn) (cl : Clause) :
    KFrag (clauseRhs c f cl).1 ∧ KFrag (clauseRhs c f cl).2 := by
  have hens : KFrag (reqPat (srtOf c f.result) (cl.ens.map (Term.kore c (canonVars c cl.vars)))) :=
    kfrag_reqPat_fg _ _ fun p hp => by
      obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp hp
      exact kfrag_kore_fg c _ t
  unfold clauseRhs
  split
  · exact ⟨kfrag_kore_fg c _ _, hens⟩
  · refine ⟨kfrag_foldrExist_fn _ (.and fun r hr => ?_) _, kfrag_reqPat_fg _ none fun _ h => by cases h⟩
    rcases List.mem_append.mp hr with hr | hr
    · rcases mem_two hr with rfl | rfl
      · exact kfrag_kore_fg c _ _
      · exact hens
    · exact kfrag_conj_fg c _ _ cl.post r hr

/-- The equation of a clause whose predicate is `\top` has the premise `⌈req = true⌉ ∧ X̄ ∈ p̄`
and the clause's right side (`clauseRhs`). -/
theorem clauseEquation_preTop_fn {f : Fn} {cl : Clause} (h : cl.pre = .top) :
    clauseEquation c f cl =
      eqnSentence c f (premise (f.args.map c.sortName) (cl.req.map (Term.kore c (canonVars c cl.vars)))
          (Term.koreList c (canonVars c cl.vars) cl.pats))
        (clauseRhs c f cl).1 (clauseRhs c f cl).2 := by
  unfold clauseEquation; simp only [withPre_top h]

/-- The equation of a clause whose predicate is `\top` under competitors has `competingPremise`'s
premise and the clause's right side (`clauseRhs`). -/
theorem competingEquation_preTop_fn {f : Fn} {others : List Clause} {cl : Clause} (h : cl.pre = .top) :
    competingEquation c f others cl =
      eqnSentence c f
        (competingPremise (f.args.map c.sortName) (others.map fun cl' => exclusion c f cl' (canonClausePres cl'))
          (cl.req.map (Term.kore c (canonVars c cl.vars))) (Term.koreList c (canonVars c cl.vars) cl.pats))
        (clauseRhs c f cl).1 (clauseRhs c f cl).2 := by
  unfold competingEquation competingPremise; simp only [withPre_top h]

/-- **The equation of a clause is a sentence at the sort variable `R` whose pattern is of the
class**, for a clause in a function whose clauses' predicates are `\top`, the sorts of the
function, of the clauses' variables and Bool being of `S`. -/
theorem rfrag_prioEquation_fn (hB : S ("Sort" ++ "Bool")) {f : Fn} {cl : Clause}
    (ha : ∀ s ∈ f.result :: f.args, S ("Sort" ++ c.sortName s))
    (hv : ∀ cl' ∈ f.clauses, ∀ s ∈ cl'.vars, S ("Sort" ++ c.sortName s))
    (hpre : ∀ cl' ∈ f.clauses, cl'.pre = .top) (hcl : cl ∈ f.clauses) :
    ∃ P, prioEquation c f cl = .axiom { sortVars := [KoreAML.Rv], pattern := P, attributes := [] } ∧
      RFrag S P ∧ KoreAML.sortOf [] P = some KoreAML.R := by
  have hargs : ∀ s ∈ f.args.map c.sortName, S ("Sort" ++ s) := fun s hs => by
    obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
    exact ha s' (List.mem_cons_of_mem _ hs')
  have hprem : RFrag S (premise (f.args.map c.sortName) (cl.req.map (Term.kore c (canonVars c cl.vars)))
      (Term.koreList c (canonVars c cl.vars) cl.pats)) :=
    rfrag_premise_fn hB hargs (fun p hp => by
      obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp hp
      exact kfrag_kore_fg c _ t) (kfrag_koreList_fg c _ _)
  have hrhs := kfrag_clauseRhs_fn c f cl
  have heq : ∀ prem, RFrag S prem → RFrag S (.implies KoreAML.R prem
      (.equals (KoreAML.srt (c.sortName f.result)) KoreAML.R
        (symApp c f.label (KoreAML.vars (KoreAML.numbered "X" 0 (f.args.map c.sortName))))
        (.and (KoreAML.srt (c.sortName f.result)) [(clauseRhs c f cl).1, (clauseRhs c f cl).2]))) :=
    fun prem hp =>
    .implies hp (.equals (ha _ (List.mem_cons_self ..))
      (by
        obtain ⟨h, xs, -, hw⟩ := symApp_head c f.label
        rw [hw]
        exact .app (fun s hs => by obtain ⟨x, -, rfl⟩ := List.mem_map.mp hs; exact ⟨_, rfl⟩)
          (kfrag_numbered_fn "X" _ 0))
      (.and fun p hp => by
        rcases mem_two hp with rfl | rfl
        · exact hrhs.1
        · exact hrhs.2))
  unfold prioEquation
  split
  · rw [clauseEquation_preTop_fn (hpre cl hcl)]
    exact ⟨_, rfl, heq _ hprem, rfl⟩
  · rw [competingEquation_preTop_fn (hpre cl hcl)]
    refine ⟨_, rfl, heq _ ?_, rfl⟩
    unfold competingPremise
    refine .and (.not (rfrag_anyOf_fn _ fun e he => ?_)) hprem
    obtain ⟨cl', hcl', rfl⟩ := List.mem_map.mp he
    have hmem : cl' ∈ f.clauses := (List.mem_filter.mp hcl').1
    exact rfrag_exclusion_fn hB f cl' _ (fun s hs => ha s (List.mem_cons_of_mem _ hs)) (hv cl' hmem)
      (hpre cl' hmem)

end

/-! ## The free variables of a pattern of the class -/

/-- A free variable of a pattern at the sort variable is an element variable of a sort constant. -/
theorem freeOf_rfrag_fn {S : String → Prop} {p : Kore.Pattern} (hp : RFrag S p) :
    ∀ (B : List VarKey) {k : VarKey}, k ∈ KoreAML.freeOf B p → ∃ n C, k = .evar n (.ctor C []) := by
  induction hp with
  | top | bottom => intro B k hk; rw [KoreAML.freeOf] at hk; exact absurd hk List.not_mem_nil
  | not _ ih => intro B k hk; rw [KoreAML.freeOf] at hk; exact ih B hk
  | and _ _ ih1 ih2 | or _ _ ih1 ih2 =>
    intro B k hk
    rw [KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOfList, List.append_nil] at hk
    rcases List.mem_append.mp hk with hk | hk
    · exact ih1 B hk
    · exact ih2 B hk
  | implies _ _ ih1 ih2 =>
    intro B k hk
    rw [KoreAML.freeOf] at hk
    rcases List.mem_append.mp hk with hk | hk
    · exact ih1 B hk
    · exact ih2 B hk
  | equals _ hp hq =>
    intro B k hk
    rw [KoreAML.freeOf] at hk
    rcases List.mem_append.mp hk with hk | hk
    · exact freeOf_kfrag_fg hp B hk
    · exact freeOf_kfrag_fg hq B hk
  | @inn C x q _ hx hq =>
    intro B k hk
    rw [KoreAML.freeOf] at hk
    rcases List.mem_append.mp hk with hk | hk
    · exact freeOf_kfrag_fg (.var ⟨C, hx⟩) B hk
    · exact freeOf_kfrag_fg hq B hk
  | exist _ _ _ ih => intro B k hk; rw [KoreAML.freeOf] at hk; exact ih _ hk

/-! ## The symbols of a translated sentence -/

/-- A symbol of the translation of a sentence's pattern is a symbol of its item. -/
theorem psyms_trAxiom_body_fn {ad : KoreAML.AxiomDecl} {σ : KoreAML.Sym}
    (hσ : σ ∈ psyms (KoreAML.tr ⟨KoreAML.tableOf ad.ax.sortVars ad.ax.pattern, []⟩ ad.ax.pattern)) :
    σ ∈ psyms (KoreAML.trAxiom [] [] ad).pat := by
  unfold KoreAML.trAxiom
  simp [psyms, ML.equal, ML.total, Pattern.equivalence, Pattern.conjunction, Pattern.disjunction,
    Pattern.negation, hσ]

/-- The sort constant of a free variable of a sentence's pattern is a symbol of its item: the
variable's guard names it. -/
theorem psyms_trAxiom_free_fn {ad : KoreAML.AxiomDecl} {x : String} {C : Kore.SortIdent}
    (hk : VarKey.evar x (.ctor C []) ∈ KoreAML.freeOf [] ad.ax.pattern) :
    KoreAML.Sym.sort C.ident.name ∈ psyms (KoreAML.trAxiom [] [] ad).pat := by
  unfold KoreAML.trAxiom
  simp only [psyms, List.mem_append]
  refine .inl (psyms_conjList_sg (w := KoreAML.guardOf (KoreAML.tableOf ad.ax.sortVars ad.ax.pattern)
    (.evar x (.ctor C []))) (List.mem_map.mpr ⟨_, List.mem_eraseDups.mpr (List.mem_append_right _ hk), rfl⟩) ?_)
  simp [KoreAML.guardOf, KoreAML.trSort_const, ML.member, psyms, KoreAML.inhOf, KoreAML.sym,
    Pattern.conjunction, Pattern.disjunction, Pattern.negation]

/-! ## The functions -/

section
variable {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
  (hD : ∀ σ, D σ → plainSym σ)
include hD

/-- A numbered sort outside `D` denotes one sort, in a model of the theory without the detached
names: its sort constant names no other sort or symbol. -/
theorem sortSing_own_fn (hI : I ⊧ᴵP Γown c D) {s : Srt} (hs : s < nRegSorts + c.sortNames.length)
    (hn : ¬ D (.sort ("Sort" ++ c.sortName s))) :
    ∃ σ, IsSort I σ ∧ ∀ a, I.evalSymb (.sort ("Sort" ++ c.sortName s)) a ↔ a = σ := by
  have hDI := defOK_own_sg hD hI
  have hcl : ∀ σ ∈ psyms (KoreAML.sortConstantItem (sortDeclOf c s)).pat, ¬ D σ := by
    intro σ hσ
    change σ ∈ psyms (KoreAML.sExists ⟨1⟩ (KoreAML.sym .sortSort)
      (KoreAML.sym (.sort ("Sort" ++ c.sortName s)) ≡ .evar ⟨1⟩)) at hσ
    simp [psyms, KoreAML.sExists, ML.member, ML.equal, ML.total, KoreAML.inhOf, KoreAML.sym,
      Pattern.equivalence, Pattern.conjunction, Pattern.disjunction, Pattern.negation] at hσ
    rcases hσ with rfl | rfl | rfl | rfl | rfl
    · exact fun h => hD _ h
    · exact fun h => hD _ h
    · exact fun h => hD _ h
    · exact fun h => hD _ h
    · exact hn
  obtain ⟨σ, h1, h2⟩ := KoreAML.sortConst_of hDI
    (hI _ (own_of_sig_sg (.inl (.inl ⟨_, sig_sortConst hs, rfl⟩)) hcl))
  exact ⟨σ, h2, h1⟩

/-- **The extension satisfies every premise of `ΓFns` that names nothing of `D`**, for a model of
`Γown c D` in which some sort has an element and names `D` that are sort constants and symbols of
the definition, where the sorts of every function and of its clauses' variables are numbered, and
every clause has the predicate `\top`. -/
theorem sat_own_fns (hI : I ⊧ᴵP Γown c D) (hne : ∃ τ, IsSort I τ ∧ ∃ m, Inh I τ m)
    (hsig : ∀ fn ∈ c.allFns, ∀ s ∈ fn.result :: fn.args, s < nRegSorts + c.sortNames.length)
    (hvars : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ∀ s ∈ cl.vars, s < nRegSorts + c.sortNames.length)
    (hpre : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.pre = .top)
    {φ : KoreAML.P} (hφ : ΓFns c φ) (hn : ∀ σ ∈ psyms φ, ¬ D σ) : extModel c D I ⊧ᴵ φ := by
  have hDI := defOK_own_sg hD hI
  have hI' : I ⊧ᴵ φ := hI _ ⟨.inl (.inl (.inl (.inl (.inr hφ)))), hn⟩
  have hc : I ⊧ᴵ KoreAML.ceilDefItem.pat := hI _ (own_of_sig_sg
    (.inl (.inl ⟨KoreAML.ceilDefItem, by unfold sigItems; simp, rfl⟩))
    (clean_of_plain_sg hD (noPlain_of_sg (by decide))))
  rcases hφ with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
  · obtain ⟨f, hf, hit⟩ := List.mem_flatMap.mp hit
    obtain ⟨sen, hsen, hs⟩ := List.mem_filterMap.mp hit
    obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp hsen
    let S : String → Prop := fun N => ∃ s, s < nRegSorts + c.sortNames.length ∧ N = "Sort" ++ c.sortName s
    obtain ⟨P, hP, hfrag, hsort⟩ := rfrag_prioEquation_fn (c := c) (S := S)
      ⟨Srt.bool, bool_numbered, by rw [sortName_bool]⟩
      (fun s hs => ⟨s, hsig f hf s hs, rfl⟩) (fun cl' hcl' s hs => ⟨s, hvars f hf cl' hcl' s hs, rfl⟩)
      (hpre f hf) hcl
    rw [hP] at hs
    obtain rfl : KoreAML.trAxiom [] [] ⟨0, "kernel",
        { sortVars := [KoreAML.Rv], pattern := P, attributes := [] }⟩ = it := Option.some.inj hs
    have hO : ∀ N, S N ∧ ¬ D (.sort N) →
        ¬ D (.sort N) ∧ ∃ σ, IsSort I σ ∧ ∀ a, I.evalSymb (.sort N) a ↔ a = σ := by
      rintro N ⟨⟨s, hs, rfl⟩, hnD⟩
      exact ⟨hnD, sortSing_own_fn hD hI hs hnD⟩
    have hRt : VarKey.sortVar "R" ∈ KoreAML.tableOf [KoreAML.Rv] P :=
      List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_cons_self ..))
    refine transfer_trAxiom_R hD hDI hc hO hne 0 "kernel" hsort (fun key hk => ?_) ?_ hI'
    · obtain ⟨n, C, rfl⟩ := freeOf_rfrag_fn hfrag [] hk
      exact ⟨n, C, rfl, hn _ (psyms_trAxiom_free_fn hk)⟩
    · refine rpred_clean_fn (rpred_rfrag_fn _ hRt hfrag [] _
        (fun k hk => List.mem_eraseDups.mpr (List.mem_append_right _ hk))
        (fun k hk => absurd hk List.not_mem_nil) fun k hk => ?_)
        fun σ hσ => hn σ (psyms_trAxiom_body_fn hσ)
      obtain ⟨n, C, rfl⟩ := freeOf_rfrag_fn hfrag [] hk
      exact List.mem_map.mpr ⟨_, List.mem_eraseDups.mpr (List.mem_filter.mpr ⟨hk, by simp⟩), rfl⟩
  · exact sat_definedness_sg x

/-- **The extension satisfies every premise of the functions, the rules, the step's closure, the
domains, the interpretation's values at silent points and the closure axiom of Bool that names
nothing of `D`**, under the hypotheses of `sat_own_fns`. -/
theorem sat_own_fns_rules (hI : I ⊧ᴵP Γown c D) (hne : ∃ τ, IsSort I τ ∧ ∃ m, Inh I τ m)
    (hsig : ∀ fn ∈ c.allFns, ∀ s ∈ fn.result :: fn.args, s < nRegSorts + c.sortNames.length)
    (hvars : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, ∀ s ∈ cl.vars, s < nRegSorts + c.sortNames.length)
    (hpre : ∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, cl.pre = .top)
    {φ : KoreAML.P}
    (hφ : ΓFns c φ ∨ ΓRules c φ ∨ Γstep c φ ∨ ΓDomains c φ ∨ ΓFallback c φ ∨ Γcl c φ)
    (hn : ∀ σ ∈ psyms φ, ¬ D σ) : extModel c D I ⊧ᴵ φ := by
  rcases hφ with hφ | hφ | hφ | hφ | hφ | hφ
  · exact sat_own_fns hD hI hne hsig hvars hpre hφ hn
  · exact sat_own_rules hD hI hφ hn
  · exact sat_own_step hD hI hφ hn
  · exact sat_own_domains hD hI hφ hn
  · exact sat_own_fallback hD hI hφ hn
  · exact sat_own_cl hD hI hφ hn

end

end KCore.Cons
