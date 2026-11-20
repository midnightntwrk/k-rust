/-
  The arity item of an instance of a sort-parametric symbol, from the text's signature.
  A declaration `symbol f{S₁,…,Sₙ}(s₁,…,sₘ) : s` has the G-arity item `arityItem`: under the guards
  `Sᵢ ∈ ⟦Sort⟧`, `f S₁ … Sₙ ⟦s₁⟧ … ⟦sₘ⟧ ⊆ ⟦s⟧`, the parameter `Sᵢ` the element variable `⟨i⟩`.
  Its instance at the sorts `C₁ … Cₙ` is the body with each `⟨i⟩` replaced by the sort constant
  `Cᵢ` (`instSubst`). Where each `Cᵢ` is a sort the text declares without parameters, its G-sort item
  says the constant denotes one element and that element is a sort; at the valuation giving `⟨i⟩`
  that element, the guards hold and the body is the instance. So the instance's item holds in every
  model of the text's signature items (`instArity_sat`, `instItem_sound`).
  - `instItem k it`: `it` is such an instance of a declaration of `k`: the sorts are read from the
    item's own head (`instSortsOf`), and the item is compared with the instantiated body, pattern for
    pattern.
  Nothing here is about K: it is about the translation of a KORE text's declarations.
-/
import KcoreSpec.FaithfulTr

set_option autoImplicit false

namespace KoreAML

open ML

/-! ## Instantiating the sort parameters -/

/-- The pattern with the element variable `⟨i⟩` replaced by `σs[i-1]`, for `1 ≤ i ≤ σs.length`;
read on patterns without binders (`instOKB`). -/
def instSubst (σs : List P) : P → P
  | .evar x => (σs[x.val - 1]?).getD (.evar x)
  | .application φ ψ => .application (instSubst σs φ) (instSubst σs ψ)
  | .implication φ ψ => .implication (instSubst σs φ) (instSubst σs ψ)
  | φ => φ

/-- The pattern has no binder and no set variable, and each of its element variables is one of
`⟨1⟩ … ⟨n⟩`. -/
def instOKB (n : Nat) : P → Bool
  | .evar x => 1 ≤ x.val && x.val ≤ n
  | .symbol _ | .bottom => true
  | .application φ ψ | .implication φ ψ => instOKB n φ && instOKB n ψ
  | _ => false

/-- The guards of a declaration's arity item: each sort parameter is a sort. -/
def arityGuards (sd : SymbolDecl) : List P :=
  let t : VarTable := paramTable sd.params
  sd.params.map fun α => sortGuard (t.ev (sortVarKey α))

/-- The body of a declaration's arity item: `f S₁ … Sₙ ⟦s₁⟧ … ⟦sₘ⟧ ⊆ ⟦s⟧`. -/
def arityBody (sd : SymbolDecl) : P :=
  let t : VarTable := paramTable sd.params
  let head := appList (sym (.symbol sd.name)) (sd.params.map fun α => .evar (t.ev (sortVarKey α)))
  let lhs := appList head (sd.args.map fun s => inhOf (trSort t s))
  lhs ⊆⊆ inhOf (trSort t sd.result)

theorem arityItem_pat_inst (sd : SymbolDecl) : (arityItem sd).pat = guarded (arityGuards sd) (arityBody sd) :=
  rfl

/-- A sort constant: the symbol of a sort name. -/
def sortSym (s : String) : P := sym (.sort s)

section
variable {M : Type} {I : Interpretation Sym M}

/-- **Instantiation**: where `⟨i⟩` takes, at `e`, the one element `v sᵢ` the constant `sortSym sᵢ`
denotes, the instantiated pattern denotes at every valuation what the pattern denotes at `e`. -/
theorem interp_instSubst {ss : List String} {v : String → M}
    (hv : ∀ s ∈ ss, ∀ b, I.evalSymb (.sort s) b ↔ b = v s) {e : Valuation M}
    (he : ∀ (i : Nat) (s : String), ss[i]? = some s → e.evalEvar ⟨i + 1⟩ = v s) (e' : Valuation M) :
    ∀ (φ : P), instOKB ss.length φ = true →
      ∀ a, (instSubst (ss.map sortSym) φ).interpret I e' a ↔ φ.interpret I e a
  | .evar x, h, a => by
    simp only [instOKB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    have hlt : x.val - 1 < ss.length := by omega
    have hs : ss[x.val - 1]? = some ss[x.val - 1] := List.getElem?_eq_getElem hlt
    have hn : x.val - 1 + 1 = x.val := by omega
    have hx : (⟨x.val - 1 + 1⟩ : EVar) = x := by rw [hn]
    have hev := he _ _ hs
    rw [hx] at hev
    simp only [instSubst, List.getElem?_map, hs, Option.map_some, Option.getD_some, sortSym]
    rw [interp_sym, hv _ (List.getElem_mem hlt), interp_evar, hev]
  | .symbol _, _, _ => Iff.rfl
  | .bottom, _, _ => Iff.rfl
  | .application φ ψ, h, a => by
    simp only [instOKB, Bool.and_eq_true] at h
    simp only [instSubst, Pattern.interpret]
    have h1 := interp_instSubst hv he e' φ h.1
    have h2 := interp_instSubst hv he e' ψ h.2
    simp only [h1, h2]
  | .implication φ ψ, h, a => by
    simp only [instOKB, Bool.and_eq_true] at h
    simp only [instSubst, Pattern.interpret]
    rw [interp_instSubst hv he e' φ h.1, interp_instSubst hv he e' ψ h.2]
  | .svar _, h, _ => by simp [instOKB] at h
  | .existential _ _, h, _ => by simp [instOKB] at h
  | .mu _ _, h, _ => by simp [instOKB] at h

/-- The G-sort item of a sort declared without parameters: the constant denotes one element, a sort. -/
theorem sortConst_one [Inhabited M] (hD : DefOK I) {d : SortDecl} (hp : d.params = [])
    (h : I ⊧ᴵ (sortConstantItem d).pat) : ∃ w, IsSort I w ∧ ∀ b, I.evalSymb (.sort d.name) b ↔ b = w := by
  obtain ⟨n, ps, hk⟩ := d
  subst hp
  have h0 := h ⟨fun _ => default, fun _ _ => False⟩ default
  simp only [sortConstantItem, paramTable, List.map_nil, guarded, appList] at h0
  rw [interp_sExists] at h0
  obtain ⟨a, ha, hq⟩ := h0
  rw [interp_member hD, interp_inhOf] at ha
  rw [interp_equal hD] at hq
  refine ⟨a, ?_, fun b => ?_⟩
  · obtain ⟨σ, hσ, hi⟩ := ha
    simp only [Function.update, interp_sym] at hσ hi
    exact ⟨σ, hσ, hi⟩
  · have := hq b
    simp only [interp_sym, interp_evar, Function.update] at this
    exact this

/-- **The instance's arity item holds** in a model of the declaration's arity item and of the G-sort
items of the instance's sorts: the body instantiated at `ss`, one sort per parameter. -/
theorem instArity_sat [Inhabited M] (hD : DefOK I) (sd : SymbolDecl) (ss : List String)
    (hlen : ss.length = sd.params.length) (hok : instOKB ss.length (arityBody sd) = true)
    (hI : I ⊧ᴵ (arityItem sd).pat)
    (hs : ∀ s ∈ ss, ∃ w, IsSort I w ∧ ∀ b, I.evalSymb (.sort s) b ↔ b = w) :
    I ⊧ᴵ instSubst (ss.map sortSym) (arityBody sd) := by
  classical
  let v : String → M := fun s => if h : ∃ w, IsSort I w ∧ ∀ b, I.evalSymb (.sort s) b ↔ b = w
    then Classical.choose h else default
  have hv : ∀ s ∈ ss, IsSort I (v s) ∧ ∀ b, I.evalSymb (.sort s) b ↔ b = v s := fun s hm => by
    have h := hs s hm
    simp only [v, h, ↓reduceDIte]
    exact Classical.choose_spec h
  let e : Valuation M := ⟨fun x => match ss[x.val - 1]? with | some s => v s | none => default,
    fun _ _ => False⟩
  have he : ∀ (i : Nat) (s : String), ss[i]? = some s → e.evalEvar ⟨i + 1⟩ = v s := fun i s h => by
    simp only [e, Nat.add_sub_cancel, h]
  intro e' m
  rw [interp_instSubst (fun s hm => (hv s hm).2) he e' _ hok]
  rw [arityItem_pat_inst] at hI
  refine interp_guarded (hI e m) fun w hw => ?_
  simp only [arityGuards, List.mem_map] at hw
  obtain ⟨α, hα, rfl⟩ := hw
  rw [sortGuard, interp_member hD, interp_sortsDomain]
  have hmem : sortVarKey α ∈ paramTable sd.params := List.mem_map_of_mem hα
  have hlt : (paramTable sd.params).idxOf (sortVarKey α) < ss.length := by
    rw [hlen, ← List.length_map (f := sortVarKey)]
    exact List.idxOf_lt_length_of_mem hmem
  have hs' := List.getElem?_eq_getElem hlt
  show IsSort I (e.evalEvar ⟨(paramTable sd.params).idxOf (sortVarKey α) + 1⟩)
  rw [he _ _ hs']
  exact (hv _ (List.getElem_mem hlt)).1

end

/-! ## The instance of a declaration of the text -/

/-- The left side of an inclusion `φ ⊆⊆ ψ`, as the translation writes it. -/
def inclLhs? : P → Option P
  | .implication (.application (.symbol .defined) (.implication (.implication l _) .bottom)) .bottom => some l
  | _ => none

/-- The head of a left-nested application and its arguments. -/
def appSpine : P → P × List P
  | .application φ ψ => ((appSpine φ).1, (appSpine φ).2 ++ [ψ])
  | φ => (φ, [])

/-- The names of a list of sort constants; none where one is not a sort constant. -/
def sortNamesOf : List P → Option (List String)
  | [] => some []
  | .symbol (.sort s) :: ps => (sortNamesOf ps).map (s :: ·)
  | _ => none

/-- The sorts an item names after its head: the first `n` arguments of its left side's head. -/
def instSortsOf (n : Nat) (φ : P) : Option (List String) :=
  (inclLhs? φ).bind fun l => sortNamesOf ((appSpine l).2.take n)

/-- **`it` is the arity item of an instance of a sort-parametric declaration of `k`**: a declaration
with parameters, sorts read from the item's head, one per parameter, each declared by `k` without
parameters, and the item is the declaration's arity body instantiated at them. -/
def instItem (k : Kore.Definition) (it : Item) : Bool :=
  k.symbolDecls.any fun sd => !sd.params.isEmpty &&
    match instSortsOf sd.params.length it.pat with
    | some ss => ss.length == sd.params.length &&
        ss.all (fun s => k.sortDecls.any fun d => d.name == s && d.params.isEmpty) &&
        instOKB ss.length (arityBody sd) && it.pat == instSubst (ss.map sortSym) (arityBody sd)
    | none => false

theorem arity_mem_sig {k : Kore.Definition} {sd : SymbolDecl} (h : sd ∈ k.symbolDecls) :
    arityItem sd ∈ (Theory.ofDefinition k).signature := by
  simp only [Theory.ofDefinition, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil]
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨sd, h, rfl⟩)))

theorem sortConst_mem_sig {k : Kore.Definition} {d : SortDecl} (h : d ∈ k.sortDecls) :
    sortConstantItem d ∈ (Theory.ofDefinition k).signature := by
  simp only [Theory.ofDefinition, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨d, h, rfl⟩))))))

/-- **Soundness of `instItem`**: such an item holds in every model of the text's signature items
(with definedness), so it is a consequence of the text's declarations. -/
theorem instItem_sound {k : Kore.Definition} {it : Item} (h : instItem k it = true) :
    itemsPremises (Theory.ofDefinition k).signature ⊧ it.pat := by
  intro M _ I hI
  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)
  have hsat : ∀ it' ∈ (Theory.ofDefinition k).signature, I ⊧ᴵ it'.pat := fun it' hm =>
    hI _ (Or.inl ⟨it', hm, rfl⟩)
  obtain ⟨sd, hsd, hb⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hb
  obtain ⟨_, hm⟩ := hb
  split at hm
  · next ss hss =>
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true] at hm
    obtain ⟨⟨⟨hlen, hdecl⟩, hok⟩, heq⟩ := hm
    rw [heq]
    refine instArity_sat hD sd ss hlen hok (hsat _ (arity_mem_sig hsd)) fun s hs => ?_
    obtain ⟨d, hd, hdn⟩ := hdecl s hs
    simp only [List.isEmpty_iff] at hdn
    obtain ⟨hn, hp⟩ := hdn
    obtain ⟨w, hw, hb⟩ := sortConst_one hD hp (hsat _ (sortConst_mem_sig hd))
    exact ⟨w, hw, hn ▸ hb⟩
  · exact absurd hm Bool.false_ne_true

end KoreAML
