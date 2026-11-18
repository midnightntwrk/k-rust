/-
  The term `Parse.term` reads from a pattern translates, through `Term.kore`, as the pattern.

  `Parse.term N vs p = .ok (t, vs')` numbers the names of p by `N` and its variables by their place
  in `vs'`; `Term.kore c ws t` writes t back with the names of the semantics `c` and the variables
  `ws`. Where `N` and `c` name the same symbols and sorts (`N.syms = c.symNames`,
  `N.sorts = c.sortNames`) and the table `tbl` holds the variable `i` of `canonVars c vars` where the
  text's table `tblT` holds the i-th variable read (`alignOK`), the two translate as one pattern
  (`term_rt`):
  `tr ⟨tblT, []⟩ p = tr ⟨tbl, []⟩ (Term.kore c (canonVars c vars) t)`.

  This holds of a pattern that is `rtPat`, a decision on the pattern. A pattern that is not is read
  as a term that `Term.kore` writes otherwise than the text does:
  - an application at sort arguments other than `inj`'s and `Lblite`'s one: the reader numbers the
    instance's name `f{X̄}` (`Parse.instName`), which `Term.kore` writes with no sort argument;
  - an application without sort arguments of a name `Term.kore` writes as `Lblite` at a sort
    (`iteSort?`), and `Lblite` at a sort whose name `iteSort?` does not give back;
  - a domain value whose text is not the text of the literal read of it (`Lit.text`).

  The variable lists: `term` appends to `vs` the variables it meets first (`vs <+: vs'`), so the
  place of a variable is its place in every later list, `vsF` the last.
-/
import KcoreSpec.ReadFns
import KcoreSpec.FaithfulStep
import KcoreSpec.NameCodes

set_option autoImplicit false

namespace KCore

namespace TermRT

open KoreAML

/-! ## Names -/

/-- A string with the prefix dropped is the prefix and the rest. -/
theorem dropPrefix_eq {pre s r : String} (h : KoreAML.Parse.dropPrefix? pre s = some r) : s = pre ++ r := by
  unfold KoreAML.Parse.dropPrefix? at h
  simp only at h
  split at h
  · rename_i h1
    have h2 : s.toList.drop pre.toList.length = r.toList := by
      have := congrArg String.toList (Option.some.inj h)
      simpa using this
    have h1' : s.toList.take pre.toList.length = pre.toList := by simpa using h1
    have h3 : s.toList = pre.toList ++ r.toList :=
      calc s.toList = s.toList.take pre.toList.length ++ s.toList.drop pre.toList.length :=
            (List.take_append_drop ..).symm
        _ = pre.toList ++ r.toList := by rw [h1', h2]
    exact String.toList_inj.mp (by rw [String.toList_append]; exact h3)
  · cases h

/-- A sort with the name X is `SortX{}`. -/
theorem sortName_srt {s : Kore.KSort} {X : String} (h : KoreAML.Parse.sortName? s = some X) : s = srt X := by
  cases s with
  | var a => simp [KoreAML.Parse.sortName?] at h
  | ctor C args =>
    cases args with
    | nil =>
      have hn := dropPrefix_eq (by simpa [KoreAML.Parse.sortName?] using h)
      obtain ⟨⟨n⟩⟩ := C
      simp only at hn
      subst hn
      rfl
    | cons _ _ => simp [KoreAML.Parse.sortName?] at h

theorem ifP {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by simp [h]

theorem ifN {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬c) : (if c then a else b) = b := by simp [h]

/-- The place `idxOf?` gives holds the name. -/
theorem getD_of_idxOf {l : List String} {n : String} {i : Nat} (h : l.idxOf? n = some i) :
    i < l.length ∧ l.getD i "" = n := by
  rw [List.idxOf?, List.findIdx?_eq_some_iff_getElem] at h
  obtain ⟨hi, hp, -⟩ := h
  refine ⟨hi, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simpa using hp

theorem need_ok {α : Type} {o : Option α} {r : Parse.RefusalReason} {d : String} {a : α}
    (h : Parse.need o r d = .ok a) : o = some a := by
  unfold Parse.need at h
  split at h
  · cases h; rfl
  · cases h

theorem bind_ok {α β : Type} {x : Parse.Rd α} {f : α → Parse.Rd β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- **The name of a symbol's number is the name numbered**, where `c` names the symbols of `N`. -/
theorem symName_of_sym {N : Parse.Names} {c : Semantics} (hs : N.syms = c.symNames) {n : String} {f : Sym}
    (h : N.sym? n = some f) : c.symName f = n := by
  have hmap : ∀ {g : Sym}, (N.syms.idxOf? n).map (nRegSyms + ·) = some g →
      ∃ j, N.syms.idxOf? n = some j ∧ g = nRegSyms + j := by
    intro g h
    cases hj : N.syms.idxOf? n with
    | none => rw [hj] at h; cases h
    | some j => rw [hj] at h; exact ⟨j, rfl, (Option.some.inj h).symm⟩
  have hreg : ∀ {g : Sym}, (match regSymNames.idxOf? n with
        | some i => some i
        | none => (N.syms.idxOf? n).map (nRegSyms + ·)) = some g →
      (∃ i, regSymNames.idxOf? n = some i ∧ g = i) ∨ ∃ j, N.syms.idxOf? n = some j ∧ g = nRegSyms + j := by
    intro g h
    split at h
    · rename_i i hi; exact .inl ⟨i, hi, (Option.some.inj h).symm⟩
    · exact .inr (hmap h)
  have key : (∃ i, regSymNames.idxOf? n = some i ∧ f = i) ∨ ∃ j, N.syms.idxOf? n = some j ∧ f = nRegSyms + j := by
    unfold Parse.Names.sym? at h
    dsimp only at h
    split at h
    · exact hreg h
    · split at h
      · exact .inr (hmap h)
      · exact hreg h
  rcases key with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · obtain ⟨hlt, hg⟩ := getD_of_idxOf hi
    rw [Faithful.regSymNames_length] at hlt
    unfold Semantics.symName
    rw [ifP hlt]
    exact hg
  · unfold Semantics.symName
    rw [ifN (Nat.not_lt.mpr (Nat.le_add_right _ _)), Nat.add_sub_cancel_left, ← hs]
    exact (getD_of_idxOf hj).2

/-- **The name of a sort's number is the name numbered**, where `c` names the sorts of `N`. -/
theorem sortName_of_srt {N : Parse.Names} {c : Semantics} (hs : N.sorts = c.sortNames) {n : String} {s : Srt}
    (h : N.srt? n = some s) : c.sortName s = n := by
  unfold Parse.Names.srt? at h
  split at h
  · rename_i i hi
    cases h
    obtain ⟨hlt, hg⟩ := getD_of_idxOf hi
    rw [Faithful.regSortNames_length] at hlt
    unfold Semantics.sortName
    rw [ifP hlt]
    exact hg
  · cases hj : N.sorts.idxOf? n with
    | none => rw [hj] at h; cases h
    | some j =>
      rw [hj] at h
      cases h
      unfold Semantics.sortName
      rw [ifN (Nat.not_lt.mpr (Nat.le_add_right _ _)), Nat.add_sub_cancel_left, ← hs]
      exact (getD_of_idxOf hj).2

theorem symE_ok {N : Parse.Names} {n : String} {f : Sym} (h : N.symE n = .ok f) : N.sym? n = some f :=
  need_ok h

theorem srtE_ok {N : Parse.Names} {n : String} {s : Srt} (h : N.srtE n = .ok s) : N.srt? n = some s :=
  need_ok h

theorem sortNameE_ok {s : Kore.KSort} {X : String} (h : Parse.sortNameE s = .ok X) : s = srt X :=
  sortName_srt (need_ok h)

/-- A sort the reader numbers s is `SortX{}`, X the name of s. -/
theorem sortE_ok {N : Parse.Names} {c : Semantics} (hs : N.sorts = c.sortNames) {S : Kore.KSort} {s : Srt}
    (h : N.sortE S = .ok s) : S = srtOf c s := by
  unfold Parse.Names.sortE at h
  obtain ⟨X, hX, h⟩ := bind_ok h
  rw [sortName_srt (need_ok hX), srtOf, sortName_of_srt hs (srtE_ok h)]

/-! ## Variables -/

/-- **The variable `varIndex` numbers**: the list is extended at its end, and the variable at the
number given is the pattern's, by name and sort. -/
theorem varIndex_spec {vs vs' : List Var} {x : Kore.EVar} {i : Nat} (h : Parse.varIndex vs x = .ok (i, vs')) :
    vs <+: vs' ∧ i < vs'.length ∧ evarKey (vs'.getD i default).kore = evarKey x := by
  unfold Parse.varIndex at h
  obtain ⟨n, hn, h⟩ := bind_ok h
  obtain ⟨s, hs, h⟩ := bind_ok h
  have hx : evarKey x = .evar ("Var" ++ n) (srt s) := by
    unfold evarKey
    rw [dropPrefix_eq (need_ok hn), sortNameE_ok hs]
  have hk : ∀ v : Var, v.name = n → v.sort = s → evarKey v.kore = evarKey x := by
    intro v h1 h2
    rw [hx, ← h1, ← h2]
    rfl
  split at h
  · rename_i j hj
    split at h
    · rename_i hsort
      cases h
      rw [List.findIdx?_eq_some_iff_getElem] at hj
      obtain ⟨hlt, hp, -⟩ := hj
      refine ⟨List.prefix_refl _, hlt, hk _ ?_ ?_⟩
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; simpa using hp
      · simpa using hsort
    · cases h
  · cases h
    refine ⟨List.prefix_append _ _, by simp, hk _ ?_ ?_⟩ <;> simp [List.getD_eq_getElem?_getD]

/-! ## The patterns whose reading `Term.kore` writes back -/

/-- The domain value `\dv{s}(text)` is read as a literal whose text is `text`. -/
def dvRT (N : Parse.Names) (s : Kore.KSort) (text : String) : Bool :=
  match N.sortE s with
  | .ok s' =>
    match Parse.lit? (((N.carriers.find? (fun p => some p.1 == KoreAML.Parse.sortName? s)).bind
        fun p => N.srt? p.2).getD s') text with
    | some l => l.text == text
    | none => false
  | .error _ => false

mutual
  /-- Every application of the pattern, under applications and conjunctions, is `inj`'s, one
  without sort arguments of a name `Term.kore` writes without (`iteSort?`), or `Lblite`'s at one
  sort whose name `iteSort?` gives back; every domain value is `dvRT`. -/
  def rtPat (N : Parse.Names) : Kore.Pattern → Bool
    | .app h ss ps =>
      (h.ident.name == "inj" ||
        (match ss with
          | [] => (iteSort? h.ident.name).isNone
          | [S] => h.ident.name == "Lblite" && (match KoreAML.Parse.sortName? S with
            | some X => iteSort? (Parse.iteName X) == some X
            | none => false)
          | _ => false)) && rtPatList N ps
    | .and _ ps => rtPatList N ps
    | .dv s text => dvRT N s text
    | _ => true
    termination_by structural p => p
  def rtPatList (N : Parse.Names) : List Kore.Pattern → Bool
    | [] => true
    | p :: ps => rtPat N p && rtPatList N ps
    termination_by structural ps => ps
end

/-- The table `tbl` holds the variable `i` of `canonVars c vars` where the text's table `tblT`
holds the i-th variable of `vsF`. -/
def alignOK (c : Semantics) (tbl tblT : VarTable) (vars : List Srt) (vsF : List Var) : Bool :=
  (List.range vsF.length).all fun i =>
    decide (tbl.ev (Faithful.canonKey c vars i) = tblT.ev (evarKey (vsF.getD i default).kore))

theorem alignOK_spec {c : Semantics} {tbl tblT : VarTable} {vars : List Srt} {vsF : List Var}
    (h : alignOK c tbl tblT vars vsF = true) {i : Nat} (hi : i < vsF.length) :
    tbl.ev (Faithful.canonKey c vars i) = tblT.ev (evarKey (vsF.getD i default).kore) := by
  unfold alignOK at h
  exact of_decide_eq_true (List.all_eq_true.mp h i (List.mem_range.mpr hi))

/-! ## The round trip -/

theorem tr_app_nil (tbl : VarTable) (h : Kore.SymbolIdent) (ss : List Kore.KSort) (ps : List Kore.Pattern) :
    tr ⟨tbl, []⟩ (.app h ss ps) = trArgs ⟨tbl, []⟩ (trSortApp tbl (sym (.symbol h.ident.name)) ss) ps := by
  rw [tr]; simp

theorem getD_of_prefix {vs vsF : List Var} (h : vs <+: vsF) {i : Nat} (hi : i < vs.length) :
    vsF.getD i default = vs.getD i default := by
  obtain ⟨ext, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

section
variable {N : Parse.Names} {c : Semantics} (hsy : N.syms = c.symNames) (hso : N.sorts = c.sortNames)
  {tbl tblT : VarTable} {vars : List Srt} {vsF : List Var}
  (hA : alignOK c tbl tblT vars vsF = true)
include hsy hso hA

/-- What `term_rt` states of a pattern. -/
def TermRT (N : Parse.Names) (c : Semantics) (tbl tblT : VarTable) (vars : List Srt) (vsF : List Var)
    (p : Kore.Pattern) : Prop :=
  ∀ (vs : List Var) (t : Term) (vs' : List Var), Parse.term N vs p = .ok (t, vs') →
    vs <+: vs' ∧ (rtPat N p = true → vs' <+: vsF →
      tr ⟨tblT, []⟩ p = tr ⟨tbl, []⟩ (Term.kore c (Faithful.canonVars c vars) t))

/-- What `terms_rt` states of a list of patterns. -/
def TermsRT (N : Parse.Names) (c : Semantics) (tbl tblT : VarTable) (vars : List Srt) (vsF : List Var)
    (ps : List Kore.Pattern) : Prop :=
  ∀ (vs : List Var) (ts : List Term) (vs' : List Var), Parse.terms N vs ps = .ok (ts, vs') →
    vs <+: vs' ∧ (rtPatList N ps = true → vs' <+: vsF →
      ∀ acc, trArgs ⟨tblT, []⟩ acc ps = trArgs ⟨tbl, []⟩ acc (Term.koreList c (Faithful.canonVars c vars) ts))

omit hsy hso in
theorem var_rt {vs vs' : List Var} {x : Kore.EVar} {i : Nat} (h : Parse.varIndex vs x = .ok (i, vs'))
    (hp : vs' <+: vsF) :
    tr ⟨tblT, []⟩ (.var (.evar x)) = tr ⟨tbl, []⟩ (varAt (Faithful.canonVars c vars) i) := by
  obtain ⟨-, hi, hk⟩ := varIndex_spec h
  have hiF : i < vsF.length := Nat.lt_of_lt_of_le hi hp.length_le
  rw [varAt, tr, tr]
  show _ = (.evar (tbl.ev (Faithful.canonKey c vars i)) : P)
  rw [alignOK_spec hA hiF, getD_of_prefix hp hi, hk]

omit hsy hso hA in
theorem termsRT_nil : TermsRT N c tbl tblT vars vsF [] := by
  intro vs ts vs' hrd
  rw [Parse.terms] at hrd
  cases hrd
  exact ⟨List.prefix_refl _, fun _ _ acc => by rw [Term.koreList, trArgs, trArgs]⟩

omit hsy hso hA in
theorem termsRT_cons {p : Kore.Pattern} {ps : List Kore.Pattern} (ih1 : TermRT N c tbl tblT vars vsF p)
    (ih2 : TermsRT N c tbl tblT vars vsF ps) : TermsRT N c tbl tblT vars vsF (p :: ps) := by
  intro vs ts vs' hrd
  rw [Parse.terms] at hrd
  obtain ⟨⟨t, vs1⟩, h1, hrd⟩ := bind_ok hrd
  obtain ⟨⟨ts1, vs2⟩, h2, hrd⟩ := bind_ok hrd
  cases hrd
  obtain ⟨p1, r1⟩ := ih1 vs t vs1 h1
  obtain ⟨p2, r2⟩ := ih2 vs1 ts1 vs' h2
  refine ⟨p1.trans p2, fun hrt hp acc => ?_⟩
  rw [rtPatList, Bool.and_eq_true] at hrt
  rw [Term.koreList, trArgs, trArgs, r1 hrt.1 (p2.trans hp), r2 hrt.2 hp]

theorem termRT_all (p : Kore.Pattern) : TermRT N c tbl tblT vars vsF p := by
  induction p using Kore.Pattern.rec
    (motive_2 := fun ps => (∀ p ∈ ps, TermRT N c tbl tblT vars vsF p) ∧ TermsRT N c tbl tblT vars vsF ps) with
  | var v =>
    intro vs t vs' hrd
    cases v with
    | evar x =>
      rw [Parse.term.eq_def] at hrd; simp only at hrd
      obtain ⟨⟨i, vs1⟩, h1, hrd⟩ := bind_ok hrd
      cases hrd
      exact ⟨(varIndex_spec h1).1, fun _ hp => by rw [Term.kore]; exact var_rt hA h1 hp⟩
    | svar X => rw [Parse.term.eq_def] at hrd; simp only at hrd; cases hrd
  | app h ss ps ih =>
    have hR : rtPat N (.app h ss ps) = true → (h.ident.name == "inj" ||
        (match ss with
          | [] => (iteSort? h.ident.name).isNone
          | [S] => h.ident.name == "Lblite" && (match KoreAML.Parse.sortName? S with
            | some X => iteSort? (Parse.iteName X) == some X
            | none => false)
          | _ => false)) = true ∧ rtPatList N ps = true := by
      intro hrt
      rw [rtPat.eq_def] at hrt
      simpa only [Bool.and_eq_true] using hrt
    intro vs t vs' hrd
    rw [Parse.term.eq_def] at hrd; simp only at hrd
    by_cases hinj : (h.ident.name == "inj") = true
    · rw [ifP hinj] at hrd
      have hname : h.ident.name = "inj" := by simpa using hinj
      obtain ⟨A, B, p, rfl, rfl⟩ : ∃ A B p, ss = [A, B] ∧ ps = [p] := by
        split at hrd
        · exact ⟨_, _, _, rfl, rfl⟩
        · cases hrd
      simp only at hrd
      obtain ⟨a, ha, hrd⟩ := bind_ok hrd
      obtain ⟨b, hb, hrd⟩ := bind_ok hrd
      by_cases hcc : N.cellPairs.contains (a, b) = true
      · rw [ifP hcc] at hrd; cases hrd
      rw [ifN hcc] at hrd
      obtain ⟨⟨t1, vs1⟩, h1, hrd⟩ := bind_ok hrd
      obtain ⟨sa, hsa, hrd⟩ := bind_ok hrd
      obtain ⟨sb, hsb, hrd⟩ := bind_ok hrd
      cases hrd
      obtain ⟨p1, r1⟩ := ih.1 p (List.mem_singleton_self _) _ _ _ h1
      refine ⟨p1, fun hrt hp => ?_⟩
      replace hrt := (hR hrt).2
      rw [rtPatList, rtPatList, Bool.and_true] at hrt
      replace hrt : True ∧ rtPat N p = true := ⟨trivial, hrt⟩
      rw [Term.kore, injP, tr_app_nil, tr_app_nil, trArgs, trArgs, trArgs, trArgs, r1 hrt.2 hp,
        sortNameE_ok ha, sortNameE_ok hb, sortName_of_srt hso (srtE_ok hsa), sortName_of_srt hso (srtE_ok hsb),
        hname]
      simp only [trSortApp, Faithful.trSort_srt]
    · rw [ifN hinj] at hrd
      by_cases hem : ss.isEmpty = true
      · rw [ifP hem] at hrd
        obtain ⟨⟨ts, vs1⟩, h1, hrd⟩ := bind_ok hrd
        obtain ⟨f, hf, hrd⟩ := bind_ok hrd
        cases hrd
        obtain ⟨p1, r1⟩ := ih.2 _ _ _ h1
        refine ⟨p1, fun hrt hp => ?_⟩
        have hss : ss = [] := List.isEmpty_iff.mp hem
        subst hss
        replace hrt := hR hrt
        have hnone : iteSort? h.ident.name = none := by
          have h0 := hrt.1
          simpa [hinj] using h0
        have hn := symName_of_sym hsy (symE_ok hf)
        rw [Term.kore, hn, hnone]
        rw [tr_app_nil, tr_app_nil, trSortApp, trSortApp, r1 hrt.2 hp]
      · rw [ifN hem] at hrd
        by_cases hal : Parse.preludeAliases.contains h.ident.name = true
        · rw [ifP hal] at hrd; cases hrd
        · rw [ifN hal] at hrd
          by_cases hite : (h.ident.name == "Lblite" && ss.length == 1) = true
          · rw [ifP hite] at hrd
            obtain ⟨S, rfl⟩ : ∃ S, ss = [S] := by
              split at hrd
              · exact ⟨_, rfl⟩
              · cases hrd
            simp only at hrd
            obtain ⟨⟨ts, vs1⟩, h1, hrd⟩ := bind_ok hrd
            obtain ⟨X, hX, hrd⟩ := bind_ok hrd
            obtain ⟨f, hf, hrd⟩ := bind_ok hrd
            cases hrd
            obtain ⟨p1, r1⟩ := ih.2 _ _ _ h1
            refine ⟨p1, fun hrt hp => ?_⟩
            have hXs : KoreAML.Parse.sortName? S = some X := need_ok hX
            replace hrt := hR hrt
            simp only [hXs] at hrt
            have hite' : iteSort? (Parse.iteName X) = some X := by
              have h0 := hrt.1
              simp [hinj] at h0
              exact h0.2
            have hl : h.ident.name = "Lblite" := by
              have h0 := hite
              simp only [Bool.and_eq_true, beq_iff_eq] at h0
              exact h0.1
            have hn := symName_of_sym hsy (symE_ok hf)
            rw [Term.kore, hn, hite']
            rw [tr_app_nil, tr_app_nil, r1 hrt.2 hp, hl, sortName_srt hXs]
            simp only [trSortApp, Faithful.trSort_srt]
          · rw [ifN hite] at hrd
            split at hrd
            · obtain ⟨⟨ts, vs1⟩, h1, hrd⟩ := bind_ok hrd
              cases hrd
              refine ⟨(ih.2 _ _ _ h1).1, fun hrt => ?_⟩
              exfalso
              have h0 := (hR hrt).1
              cases ss with
              | nil => simp at hem
              | cons S ss' =>
                cases ss' with
                | nil => simp [hinj] at h0 hite; exact hite h0.1
                | cons _ _ => simp [hinj] at h0
            · cases hrd
  | and s ps ih =>
    intro vs t vs' hrd
    cases ps with
    | nil => rw [Parse.term.eq_def] at hrd; simp only at hrd; cases hrd
    | cons p ps1 =>
      cases ps1 with
      | nil => rw [Parse.term.eq_def] at hrd; simp only at hrd; cases hrd
      | cons q ps2 =>
        cases ps2 with
        | cons _ _ => rw [Parse.term.eq_def] at hrd; simp only at hrd; cases hrd
        | nil =>
          cases q with
          | var v =>
            cases v with
            | evar x =>
              rw [Parse.term.eq_def] at hrd; simp only at hrd
              obtain ⟨⟨t1, vs1⟩, h1, hrd⟩ := bind_ok hrd
              obtain ⟨⟨i, vs2⟩, h2, hrd⟩ := bind_ok hrd
              cases hrd
              obtain ⟨p1, r1⟩ := ih.1 p (List.mem_cons_self ..) vs t1 vs1 h1
              have p2 := (varIndex_spec h2).1
              refine ⟨p1.trans p2, fun hrt hp => ?_⟩
              rw [rtPat.eq_def] at hrt
              simp only at hrt
              rw [rtPatList, Bool.and_eq_true] at hrt
              show sAnd (tr ⟨tblT, []⟩ p) (tr ⟨tblT, []⟩ (.var (.evar x))) =
                sAnd (tr ⟨tbl, []⟩ (Term.kore c (Faithful.canonVars c vars) t1))
                  (tr ⟨tbl, []⟩ (varAt (Faithful.canonVars c vars) i))
              rw [r1 hrt.1 (p2.trans hp), var_rt hA h2 hp]
            | svar X => rw [Parse.term.eq_def] at hrd; simp only at hrd; cases hrd
          | _ => rw [Parse.term.eq_def] at hrd; simp only at hrd; cases hrd
  | dv s text =>
    intro vs t vs' hrd
    rw [Parse.term.eq_def] at hrd; simp only at hrd
    obtain ⟨s', hs', hrd⟩ := bind_ok hrd
    obtain ⟨l, hl, hrd⟩ := bind_ok hrd
    cases hrd
    refine ⟨List.prefix_refl _, fun hrt _ => ?_⟩
    rw [rtPat.eq_def] at hrt
    simp only at hrt
    rw [dvRT, hs'] at hrt
    dsimp only at hrt
    rw [need_ok hl] at hrt
    have ht : l.text = text := by simpa using hrt
    rw [Term.kore, tr, tr, ht, sortE_ok hso hs', srtOf, Faithful.trSort_srt, Faithful.trSort_srt]
  | nil => exact ⟨fun p hp => absurd hp List.not_mem_nil, termsRT_nil⟩
  | cons p ps ih1 ih2 =>
    refine ⟨fun q hq => ?_, termsRT_cons ih1 ih2.2⟩
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ih1
    · exact ih2.1 q hq
  | _ =>
    intro vs t vs' hrd
    rw [Parse.term.eq_def] at hrd
    simp only at hrd
    first | cases hrd | (split at hrd <;> first | cases hrd | (split at hrd <;> cases hrd))

theorem termsRT_all : ∀ ps : List Kore.Pattern, TermsRT N c tbl tblT vars vsF ps
  | [] => termsRT_nil
  | p :: ps => termsRT_cons (termRT_all hsy hso hA p) (termsRT_all ps)

/-- **The term `Parse.term` reads of a pattern translates as the pattern.** Where `N` and `c` name
the same symbols and sorts, the tables are aligned on the variables `vsF` (`alignOK`), the pattern
is `rtPat` and the variables read are among the first of `vsF`. -/
theorem term_rt {vs vs' : List Var} {p : Kore.Pattern} {t : Term} (h : Parse.term N vs p = .ok (t, vs'))
    (hrt : rtPat N p = true) (hp : vs' <+: vsF) :
    tr ⟨tblT, []⟩ p = tr ⟨tbl, []⟩ (Term.kore c (Faithful.canonVars c vars) t) :=
  (termRT_all hsy hso hA p vs t vs' h).2 hrt hp

/-- The arguments `Parse.terms` reads translate as the patterns, applied to one pattern. -/
theorem terms_rt {vs vs' : List Var} {ps : List Kore.Pattern} {ts : List Term}
    (h : Parse.terms N vs ps = .ok (ts, vs')) (hrt : rtPatList N ps = true) (hp : vs' <+: vsF) (acc : P) :
    trArgs ⟨tblT, []⟩ acc ps = trArgs ⟨tbl, []⟩ acc (Term.koreList c (Faithful.canonVars c vars) ts) :=
  (termsRT_all hsy hso hA ps vs ts vs' h).2 hrt hp acc

end

/-- A semantics with the names of `N`. -/
def semOf (N : Parse.Names) : Semantics :=
  { lib := {}, sortNames := N.sorts, symNames := N.syms, userSorts := [], ctors := [], fns := [], userSubsorts := [],
    pgmSort := Srt.k, rules := [] }

/-- `Parse.term` extends the list of variables at its end. -/
theorem term_prefix {N : Parse.Names} {vs vs' : List Var} {p : Kore.Pattern} {t : Term}
    (h : Parse.term N vs p = .ok (t, vs')) : vs <+: vs' :=
  (termRT_all (c := semOf N) rfl rfl (tbl := []) (tblT := []) (vars := []) (vsF := []) rfl p vs t vs' h).1

/-- `Parse.terms` extends the list of variables at its end. -/
theorem terms_prefix {N : Parse.Names} {vs vs' : List Var} {ps : List Kore.Pattern} {ts : List Term}
    (h : Parse.terms N vs ps = .ok (ts, vs')) : vs <+: vs' :=
  (termsRT_all (c := semOf N) rfl rfl (tbl := []) (tblT := []) (vars := []) (vsF := []) rfl ps vs ts vs' h).1

end TermRT

end KCore
