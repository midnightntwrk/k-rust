/-
  KCore. The decoder of an instance name: the head and the sort names of `h{x₁,…,xₙ}`, the name
  `Parse.instName h [x₁, …, xₙ]` gives the instance of the sort-parametric symbol `h` at the sorts
  `x₁ … xₙ`.
  - `instDecode?` reads a name as `h{x₁,…,xₙ}` with n ≥ 1, `h` non-empty and holding no `{`, each
    `xᵢ` non-empty and holding no `,`, `{` or `}` (`InstNameOK`), and gives none for every other
    name. It is defined by structural recursion on the name's characters, so the kernel evaluates
    it on a literal.
  - It is the exact inverse of the writing: `instDecode?_instName` (a writing under `InstNameOK`
    decodes to its parts) and `instDecode?_eq_some` (a decoding is such a writing), hence
    `instDecode?_inj` (two names with one decoding are one name).
  Imports no module of the library, so the writers of applications can read it.
-/

namespace KCore

/-- A character a sort name of an instance name may hold: none of `,`, `{`, `}`. -/
def instSortChar (c : Char) : Prop := c ≠ ',' ∧ c ≠ '{' ∧ c ≠ '}'

instance (c : Char) : Decidable (instSortChar c) := by unfold instSortChar; infer_instance

/-- The conditions under which `h{x₁,…,xₙ}` is read back as `h` at `x₁ … xₙ`: the head is
non-empty and holds no `{`; there is at least one sort name; each is non-empty and holds only
`instSortChar` characters. -/
def InstNameOK (h : String) (xs : List String) : Prop :=
  h.toList ≠ [] ∧ '{' ∉ h.toList ∧ xs ≠ [] ∧ ∀ x ∈ xs, x.toList ≠ [] ∧ ∀ c ∈ x.toList, instSortChar c

instance (h : String) (xs : List String) : Decidable (InstNameOK h xs) := by
  unfold InstNameOK; infer_instance

/-- The characters of a name before its first `{`, and those after it; none without a `{`. -/
def instDecHead : List Char → Option (List Char × List Char)
  | [] => none
  | c :: cs => if c = '{' then some ([], cs) else (instDecHead cs).map fun p => (c :: p.1, p.2)

/-- `c` put before the first part. -/
def instDecPush (c : Char) : List (List Char) → List (List Char)
  | [] => [[c]]
  | p :: ps => (c :: p) :: ps

/-- The parts of `x₁,…,xₙ}`, split at each `,`, the text ending at its first `}`: none where a
`{` occurs, where no `}` closes it, or where characters follow the `}`. A part may be empty here;
the result is never `[]`. -/
def instDecBody : List Char → Option (List (List Char))
  | [] => none
  | c :: cs =>
    if c = '}' then (if cs.isEmpty then some [[]] else none)
    else if c = ',' then (instDecBody cs).map ([] :: ·)
    else if c = '{' then none
    else (instDecBody cs).map (instDecPush c)

/-- The head and the sort names of an instance name `h{x₁,…,xₙ}` (`Parse.instName`), n ≥ 1, the
head non-empty without `{`, each sort name non-empty without `,`, `{`, `}`; none for every other
name. -/
def instDecode? (n : String) : Option (String × List String) :=
  match instDecHead n.toList with
  | some (h, rest) =>
    match instDecBody rest with
    | some ps =>
      if !h.isEmpty && ps.all (fun p => !p.isEmpty) then some (String.ofList h, ps.map String.ofList)
      else none
    | none => none
  | none => none

/-! ## The head -/

theorem instDecHead_eq_some {cs h r : List Char} :
    instDecHead cs = some (h, r) ↔ cs = h ++ '{' :: r ∧ '{' ∉ h := by
  induction cs generalizing h with
  | nil =>
    simp only [instDecHead, reduceCtorEq, false_iff, not_and]
    intro hh; cases h <;> simp at hh
  | cons c cs ih =>
    by_cases hc : c = '{'
    · subst hc
      simp only [instDecHead, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩; simp
      · rintro ⟨he, hn⟩
        cases h with
        | nil => simp_all
        | cons d h => simp at he hn; exact absurd he.1 (fun e => hn.1 e)
    · simp only [instDecHead, hc, ↓reduceIte, Option.map_eq_some_iff, Prod.exists]
      constructor
      · rintro ⟨a, b, hab, he⟩
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨rfl, hn⟩ := (ih (h := a)).1 hab
        refine ⟨rfl, ?_⟩
        simp only [List.mem_cons, not_or]
        exact ⟨fun e => hc e.symm, hn⟩
      · rintro ⟨he, hn⟩
        cases h with
        | nil => simp at he; exact absurd he.1 hc
        | cons d h =>
          simp only [List.cons_append, List.cons.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          refine ⟨h, r, (ih (h := h)).2 ⟨rfl, fun hm => hn (List.mem_cons_of_mem _ hm)⟩, rfl⟩

/-! ## The body -/

/-- The writing `x₁,…,xₙ}` of the sort names. -/
abbrev instBodyText (ps : List (List Char)) : List Char := [','].intercalate ps ++ ['}']

theorem instDecBody_ne_nil {cs : List Char} {ps : List (List Char)} (h : instDecBody cs = some ps) :
    ps ≠ [] := by
  induction cs generalizing ps with
  | nil => simp [instDecBody] at h
  | cons c cs ih =>
    unfold instDecBody at h
    split at h
    · split at h
      · cases h; simp
      · simp at h
    split at h
    · obtain ⟨q, -, rfl⟩ := Option.map_eq_some_iff.1 h; simp
    split at h
    · simp at h
    · obtain ⟨q, -, rfl⟩ := Option.map_eq_some_iff.1 h
      cases q <;> simp [instDecPush]

theorem instDecPush_text (c : Char) {ps : List (List Char)} (h : ps ≠ []) :
    instBodyText (instDecPush c ps) = c :: instBodyText ps := by
  match ps, h with
  | [p], _ => simp [instDecPush, instBodyText]
  | p :: q :: ps, _ => simp [instDecPush, instBodyText, List.intercalate_cons_cons]

/-- A decoding of the body is the writing of its parts, and no part holds `,`, `{` or `}`. -/
theorem instDecBody_eq_some {cs : List Char} {ps : List (List Char)} (h : instDecBody cs = some ps) :
    cs = instBodyText ps ∧ ∀ p ∈ ps, ∀ c ∈ p, instSortChar c := by
  induction cs generalizing ps with
  | nil => simp [instDecBody] at h
  | cons c cs ih =>
    unfold instDecBody at h
    split at h
    · rename_i hc
      split at h
      · rename_i he
        simp only [Option.some.injEq] at h; subst h
        simp only [List.isEmpty_iff] at he; subst he; subst hc
        simp [instBodyText]
      · simp at h
    split at h
    · rename_i _ hc
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨rfl, hcl⟩ := ih hq
      have hne := instDecBody_ne_nil hq
      subst hc
      refine ⟨?_, ?_⟩
      · match q, hne with
        | q :: qs, _ => simp [instBodyText, List.intercalate_cons_cons]
      · intro p hp; simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · simp
        · exact hcl p hp
    split at h
    · simp at h
    · rename_i h1 h2 h3
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨rfl, hcl⟩ := ih hq
      have hne := instDecBody_ne_nil hq
      refine ⟨(instDecPush_text c hne).symm, ?_⟩
      match q, hne with
      | q :: qs, _ =>
        intro p hp
        simp only [instDecPush, List.mem_cons] at hp
        rcases hp with rfl | hp
        · intro d hd; simp only [List.mem_cons] at hd
          rcases hd with rfl | hd
          · exact ⟨h2, h3, h1⟩
          · exact hcl q (List.mem_cons_self ..) d hd
        · exact hcl p (List.mem_cons_of_mem _ hp)

/-- A part of `instSortChar` characters is read through. -/
theorem instDecBody_append {x rest : List Char} (hx : ∀ c ∈ x, instSortChar c) (hne : x ≠ []) :
    instDecBody (x ++ rest) = (instDecBody rest).map fun ps =>
      match ps with
      | [] => [x]
      | p :: ps => (x ++ p) :: ps := by
  induction x with
  | nil => exact absurd rfl hne
  | cons c x ih =>
    have ⟨h1, h2, h3⟩ := hx c (List.mem_cons_self ..)
    simp only [List.cons_append, instDecBody, h3, ↓reduceIte, h1, h2]
    cases x with
    | nil =>
      simp only [List.nil_append]
      cases instDecBody rest with
      | none => rfl
      | some ps => cases ps <;> rfl
    | cons d x =>
      rw [ih (fun c hc => hx c (List.mem_cons_of_mem _ hc)) (by simp)]
      cases instDecBody rest with
      | none => rfl
      | some ps => cases ps <;> rfl

/-- The writing of parts of `instSortChar` characters, each non-empty, decodes to the parts. -/
theorem instDecBody_text {ps : List (List Char)} (hne : ps ≠ [])
    (hp : ∀ p ∈ ps, p ≠ [] ∧ ∀ c ∈ p, instSortChar c) :
    instDecBody (instBodyText ps) = some ps := by
  induction ps with
  | nil => exact absurd rfl hne
  | cons p ps ih =>
    have ⟨hpne, hpc⟩ := hp p (List.mem_cons_self ..)
    cases ps with
    | nil =>
      simp only [instBodyText, List.intercalate_singleton]
      rw [instDecBody_append hpc hpne]
      simp [instDecBody]
    | cons q qs =>
      have ih' := ih (by simp) (fun p' hp' => hp p' (List.mem_cons_of_mem _ hp'))
      simp only [instBodyText, List.intercalate_cons_cons, List.append_assoc]
      rw [instDecBody_append hpc hpne]
      simp only [instBodyText] at ih'
      simp [instDecBody, ih']

/-! ## The decoder -/

theorem instDecName_toList (h : String) (xs : List String) :
    (h ++ "{" ++ ",".intercalate xs ++ "}").toList =
      h.toList ++ '{' :: instBodyText (xs.map String.toList) := by
  simp [String.toList_append, String.toList_intercalate, instBodyText]

/-- An instance name under `InstNameOK` decodes to its head and sort names. `Parse.instName h xs`
is this name. -/
theorem instDecode?_instName {h : String} {xs : List String} (ok : InstNameOK h xs) :
    instDecode? (h ++ "{" ++ ",".intercalate xs ++ "}") = some (h, xs) := by
  obtain ⟨hne, hnb, xsne, hxs⟩ := ok
  have hd : instDecHead (h ++ "{" ++ ",".intercalate xs ++ "}").toList =
      some (h.toList, instBodyText (xs.map String.toList)) :=
    instDecHead_eq_some.2 ⟨instDecName_toList h xs, hnb⟩
  have hb : instDecBody (instBodyText (xs.map String.toList)) = some (xs.map String.toList) :=
    instDecBody_text (by simpa using xsne) (by
      intro p hp
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hp
      exact hxs x hx)
  unfold instDecode?
  rw [hd]
  simp only [hb]
  have h1 : (!h.toList.isEmpty) = true := by simpa using hne
  have h2 : (xs.map String.toList).all (fun p => !p.isEmpty) = true := by
    simp only [List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff]
    exact fun x hx => (hxs x hx).1
  simp [h1, h2, String.ofList_toList, List.map_map]

/-- A decoding is the writing of its parts, under `InstNameOK`. -/
theorem instDecode?_eq_some {n h : String} {xs : List String} (hd : instDecode? n = some (h, xs)) :
    InstNameOK h xs ∧ n = h ++ "{" ++ ",".intercalate xs ++ "}" := by
  unfold instDecode? at hd
  split at hd
  · rename_i hh r hhd
    obtain ⟨hn, hnb⟩ := instDecHead_eq_some.1 hhd
    split at hd
    · rename_i ps hps
      obtain ⟨hr, hcl⟩ := instDecBody_eq_some hps
      have hpne := instDecBody_ne_nil hps
      split at hd
      · rename_i hc
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff,
          List.all_eq_true] at hc
        simp only [Option.some.injEq, Prod.mk.injEq] at hd
        obtain ⟨rfl, rfl⟩ := hd
        refine ⟨⟨by simpa using hc.1, by simpa using hnb, by simpa using hpne, ?_⟩, ?_⟩
        · intro x hx
          obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
          have := hc.2 p hp
          exact ⟨by simpa using this, by simpa using hcl p hp⟩
        · apply String.ext
          rw [instDecName_toList, hn, hr]
          simp [List.map_map, String.toList_ofList]
      · simp at hd
    · simp at hd
  · simp at hd

/-- Two names with one decoding are one name. -/
theorem instDecode?_inj {n n' : String} {p : String × List String}
    (h : instDecode? n = some p) (h' : instDecode? n' = some p) : n = n' := by
  obtain ⟨hh, xs⟩ := p
  rw [(instDecode?_eq_some h).2, (instDecode?_eq_some h').2]

end KCore
