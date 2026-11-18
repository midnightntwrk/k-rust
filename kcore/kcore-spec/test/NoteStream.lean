/-
  The tie (C14) of the readings `reflectionAsOwn` and `streamRule` on their construct fixture
  e2-cells-stream: `configuration <t> <k> $PGM:Exp </k> <in stream="stdin"> .List </in>
  <out stream="stdout"> .List </out> </t>` with INT and LIST imported. The text is
  `f2-examples/cellsstream.kompile.kore`, the kompiled text that
  `test/constructs/fixtures/e2-cells-stream/kompile.txt` records (sha256 fce5e727…), with its paths
  restored. Run from the package root: `lake env lean -j1 test/NoteStream.lean`. Every statement is
  on the literal `defn`, for every interpretation H; nothing reads `Parse.parse` or `emit`. Only
  the sentences of the two readings are tied here; the text's other 3317 sentences are those of
  any definition importing K-IO, LIST and INT, which the files of the other fixtures tie by class.

  Layer 1. `coreOK` (kernel). `attrsAgree` holds of this text by the compiled check; its kernel
  decision is not stated here (its hooks part alone peaks at 10 GiB on this text). What it compares
  for the two readings is stated on their sentences: the seven hooks are interpreted by no registry
  hook and each symbol is a parameter of none (`refl_hooks`, `refl_params`), and each rule's
  priority is its sentence's (`rule_prios`).

  `reflectionAsOwn`: the eight sentences read so are K-REFLECTION's declarations of `#argv`,
  `#configuration`, `#fresh`, `#getenv`, `#kompiledDirectory`, `#sort` and `getsymbol` (hooked
  symbols) and of the constructor `#noParse`. Class *entailed* (G-arity, the declaration's
  class): each declares a symbol of Γ without sort parameters, and its arity item is Γ's item of
  that symbol (`refl_arity`, kernel), so Γ entails it for every H (`refl_entailed`). The seven
  hooked symbols are parameter symbols of no registry hook (`refl_params`), `#noParse` a
  constructor. The expectation, form (c): the text states nothing of a parameter's value but its
  arity, and its value is the interpretation's, kept where it has the declared sort
  (`refl_value`, for every H); the reached point is test/Guards.lean's `DevRefl.go_step_Hk` (under
  one interpretation a rule applying `#configuration` steps, under `HookParams.none` it does not,
  test/Configuration.lean `stuck_go`).

  `streamRule`: the eight rewrite axioms of the stream modules that kompile writes into the user
  module (sentences 2815 to 2822, labelled `STDIN-STREAM.…` and `STDOUT-STREAM.…`, priorities
  30, 50, 50, 50, 200, 25, 25, 25) are the definition's eight rules (`rule_texts`), each read with
  the text's priority (`rule_prios`). Class *weaker* (a rule, `ruleRightDefined` and the priority
  premise): Γ's axiom of each rule is the text's sentence with conjuncts more on its left side (the
  negation of the rules of a smaller priority, and `⌈r⌉`); the sentence is the item of
  `\rewrites{C}(Ltext, r)` at the table of Γ's axiom, `Ltext` the first two conjuncts of Γ's left
  side (`rules_tied`, kernel), so the sentence entails Γ's item (`rules_from_text`, W1,
  `TieRuleLhs.rule_w1`), for every H.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.NoteStream

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/cellsstream.kompile.kore"
definition_of defn from "f2-examples/cellsstream.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- No parameter of the definition is an open generator. -/
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl

/-! ## Layer 1 -/

theorem coreOK : c.coreOK = true := by decide_cheap

/-! ## `reflectionAsOwn` -/

/-- The symbols of K-REFLECTION's sentences read as the definition's own. -/
def reflNames : List String :=
  ["Lbl'Hash'argv'LParRParUnds'K-REFLECTION'Unds'List", "Lbl'Hash'configuration'Unds'K-REFLECTION'Unds'K",
   "Lbl'Hash'fresh'LParUndsRParUnds'K-REFLECTION'Unds'KItem'Unds'String",
   "Lbl'Hash'getenv'LParUndsRParUnds'K-REFLECTION'Unds'K'Unds'String",
   "Lbl'Hash'kompiledDirectory'LParRParUnds'K-REFLECTION'Unds'String", "Lbl'Hash'noParse",
   "Lbl'Hash'sort'LParUndsRParUnds'K-REFLECTION'Unds'String'Unds'K",
   "Lblgetsymbol'LParUndsRParUnds'K-REFLECTION'Unds'KItem'Unds'K"]

/-- Their declarations in the text. -/
noncomputable def reflDecls : List SymbolDecl := kore.symbolDecls.filter (reflNames.contains ·.name)

theorem reflDecls_names : reflDecls.map (·.name) = reflNames := by decide +kernel

/-- Γ's symbol of the name `n`, where it has one. -/
noncomputable def sigOf (n : String) : Option CtorSig := (kernelSyms c).find? (c.symName ·.name == n)

/-- **Each declaration is of a symbol of Γ, without sort parameters, and its arity item is Γ's
item of that symbol** (kernel). -/
theorem refl_arity : reflDecls.all (fun sd => match sigOf sd.name with
    | some k => sd.params.isEmpty && decide ((arityItem sd).pat = (symArityItem c k).pat)
    | none => false) = true := by
  decide +kernel

kernel_rfl sigItems_withHooks : ∀ (c : Semantics) (H : HookParams), sigItems (c.withHooks H) = sigItems c

/-- **E for the eight declarations**: Γ entails each one's arity item, for every H. -/
theorem refl_entailed (H : HookParams) : ∀ sd ∈ reflDecls, Γ (cH H) ⊧ (arityItem sd).pat := by
  intro sd hsd M _ I hI
  have h := List.all_eq_true.mp refl_arity sd hsd
  cases hk : sigOf sd.name with
  | none => rw [hk] at h; cases h
  | some k =>
    rw [hk] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.2]
    have hmem : k ∈ kernelSyms c := List.mem_of_find?_eq_some hk
    exact sat_sigItem hI (by rw [sigItems_withHooks]; exact sig_arity hmem)

/-- The seven hooks the text gives the K-REFLECTION symbols are interpreted by no registry hook. -/
theorem refl_hooks : ["KREFLECTION.argv", "KREFLECTION.configuration", "KREFLECTION.fresh", "KREFLECTION.getenv",
    "KREFLECTION.kompiledDir", "KREFLECTION.sort", "KREFLECTION.getKLabel"].all (regHookOf · == none) = true := by
  decide +kernel

/-- The seven hooked symbols are parameter symbols of no registry hook and no open generator; the
eighth, `#noParse`, is a constructor. -/
theorem refl_params : (reflNames.filter (· != "Lbl'Hash'noParse")).all (fun n =>
      c.params.any fun p => c.symName p.sig.name == n && p.impl.isNone && !p.raw) = true ∧
    c.ctorSigs.any (c.symName ·.name == "Lbl'Hash'noParse") = true := by
  decide +kernel

/-- **The expectation (form (c))**: for every H, the value of a parameter symbol with no registry
hook and no open generator is the interpretation's answer, kept where it has the declared sort:
the text states nothing else of it. -/
theorem refl_value (H : HookParams) (k : ParamSig) (hk : c.lookupParam k.sig.name = some k)
    (hi : k.impl = none) (hraw : k.raw = false) (vs : List GroundTerm) :
    (cH H).paramVal k.sig.name vs = (H.app k.sig.name vs).filter fun v => (cH H).sortOf v == some k.sig.result := by
  have hl : (cH H).lookupParam k.sig.name = c.lookupParam k.sig.name := rfl
  unfold Semantics.paramVal
  rw [hl, hk]
  simp only [hi, hraw, Bool.false_eq_true, ↓reduceIte]
  rfl

/-! ## `streamRule` -/

/-- The text's eight stream rules, in the order of `defn`'s rules. -/
noncomputable def ruleText : List AxiomDecl := (kore.axiomDecls.drop 2814).take 8

theorem rule_texts : ruleText.map (fun ad => (ad.index, ad.module, AttrsAgree.strArg ad.ax.attributes "label")) =
    [(2815, "E2-CELLS-STREAM", some "STDOUT-STREAM.stdoutWrite"), (2816, "E2-CELLS-STREAM", some "STDIN-STREAM.stdinTrim"),
     (2817, "E2-CELLS-STREAM", some "STDIN-STREAM.stdinParseInt"),
     (2818, "E2-CELLS-STREAM", some "STDIN-STREAM.stdinParseString"),
     (2819, "E2-CELLS-STREAM", some "STDIN-STREAM.stdinGetc"),
     (2820, "E2-CELLS-STREAM", some "STDOUT-STREAM.stdoutBufferFloat"),
     (2821, "E2-CELLS-STREAM", some "STDOUT-STREAM.stdoutBufferInt"),
     (2822, "E2-CELLS-STREAM", some "STDOUT-STREAM.stdoutBufferString")] := by
  decide +kernel

/-- The rules are the eight, each of the priority its sentence states. -/
theorem rule_prios : c.rules.map (·.prio) = ruleText.map (AttrsAgree.prioOf ·.ax.attributes) ∧
    c.rules.map (·.prio) = [30, 50, 50, 50, 200, 25, 25, 25] := by
  decide +kernel

/-- The first two conjuncts of a conjunction of at least two. -/
def lhsTwo : Kore.Pattern → Option (Kore.Pattern × Kore.Pattern)
  | .and _ (a :: b :: _) => some (a, b)
  | _ => none

theorem lhsTwo_sub {M : Type} {I : Interpretation KoreAML.Sym M} {L a b : Kore.Pattern} (C : Kore.KSort)
    (h : lhsTwo L = some (a, b)) {t : VarTable} {e : Valuation M} {x : M}
    (hx : (tr ⟨t, []⟩ L).interpret I e x) : (tr ⟨t, []⟩ (.and C [a, b])).interpret I e x := by
  unfold lhsTwo at h
  split at h
  · rename_i S ps
    cases h
    rw [interp_and (List.cons_ne_nil _ _)] at hx
    rw [interp_and (List.cons_ne_nil _ _)]
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hx _ (List.mem_cons_self ..)
    · rw [List.mem_singleton.mp hp]; exact hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · cases h

/-- Rule `r` and sentence `ad` are read together: Γ's axiom of `r` is `\rewrites{C}(L', r')`,
`L'` a conjunction whose first two conjuncts are `a` and `b`, and the sentence is the item of
`\rewrites{C}(\and{C}(a, b), r')` at the table of Γ's axiom (its free variables Γ's). -/
noncomputable def tieB (r : Rule) (ad : AxiomDecl) : Bool :=
  match TieRuleLhs.rwParts (prioRuleK c r) with
  | none => false
  | some (C, L, rr) => match lhsTwo L with
    | none => false
    | some (a, b) =>
      decide (TiePair.renSeq (TieRuleLhs.itemAt (tableOf [] (prioRuleK c r))
          (freeOf [] (.rewrites C (.and C [a, b]) rr)).eraseDups C (.and C [a, b]) rr) [] = some (trS ad).pat) &&
        (freeOf [] (.rewrites C (.and C [a, b]) rr)).eraseDups.all
          (fun k => (freeOf [] (prioRuleK c r)).eraseDups.contains k)

/-- **W1 from `tieB`**: the sentence entails Γ's axiom of the rule. -/
theorem w1_of_tieB {r : Rule} {ad : AxiomDecl} (h : tieB r ad = true) {M : Type} [Inhabited M]
    {I : Interpretation KoreAML.Sym M} (hD : DefOK I) (hT : I ⊧ᴵ (trS ad).pat) :
    I ⊧ᴵ (trAxiom [] [] ⟨0, "kernel", ⟨[], prioRuleK c r, []⟩⟩).pat := by
  unfold tieB at h
  cases hq : TieRuleLhs.rwParts (prioRuleK c r) with
  | none => simp only [hq] at h; cases h
  | some q =>
    obtain ⟨C, L, rr⟩ := q
    cases hl : lhsTwo L with
    | none => simp only [hq, hl] at h; cases h
    | some ab =>
      obtain ⟨a, b⟩ := ab
      simp only [hq, hl, Bool.and_eq_true, decide_eq_true_eq] at h
      exact TieRuleLhs.rule_w1 hD hq h.1 h.2 hT fun _ _ _ x hx => lhsTwo_sub C hl hx

theorem rules_length : c.rules.length = 8 ∧ ruleText.length = 8 := by decide +kernel

/-- **Each rule and its sentence are read together** (kernel). -/
theorem rules_tied : (c.rules.zip ruleText).all (fun p => tieB p.1 p.2) = true := by decide +kernel

/-- **W1 for the stream rules, and the converse for `ruleItems`**: the j-th item is a consequence
of the j-th stream rule's sentence, for every H. -/
theorem rules_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (ruleItems (cH H))[j]? = some it →
      ∃ ad, ruleText[j]? = some ad ∧ (TiePair.Texts [(trS ad).pat] ⊧ it.pat) := by
  intro j it hj
  rw [TiePair.ruleItems_withHooks] at hj
  unfold ruleItems at hj
  rw [List.getElem?_map] at hj
  cases hr : c.rules[j]? with
  | none => rw [hr] at hj; cases hj
  | some r =>
    rw [hr] at hj
    have hit := (Option.some.inj hj).symm
    have hjr : j < c.rules.length := (List.getElem?_eq_some_iff.mp hr).1
    have hjt : j < ruleText.length := by rw [rules_length.2]; rw [rules_length.1] at hjr; exact hjr
    refine ⟨ruleText[j], List.getElem?_eq_getElem hjt, ?_⟩
    subst hit
    have hp : (r, ruleText[j]) ∈ c.rules.zip ruleText :=
      List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨hr, List.getElem?_eq_getElem hjt⟩)
    intro M _ I hI
    exact w1_of_tieB (List.all_eq_true.mp rules_tied _ hp) (TiePair.defOK_texts hI)
      (hI _ (Or.inl (List.mem_singleton_self _)))

end KCore.NoteStream

#print axioms KCore.NoteStream.coreOK
#print axioms KCore.NoteStream.refl_hooks
#print axioms KCore.NoteStream.refl_arity
#print axioms KCore.NoteStream.refl_entailed
#print axioms KCore.NoteStream.refl_params
#print axioms KCore.NoteStream.refl_value
#print axioms KCore.NoteStream.rule_texts
#print axioms KCore.NoteStream.rule_prios
#print axioms KCore.NoteStream.rules_tied
#print axioms KCore.NoteStream.rules_from_text
