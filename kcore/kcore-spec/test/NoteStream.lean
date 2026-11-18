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

  `consistent` for every H (no fact named; the semantics is `plain`). The expectation (C7 form (a),
  by the executable step under `execReady`), from `Pre H` (the function equations as written, Γ's
  items pattern for pattern, `shape`, `append`'s two from the module KSEQ; Γ's rule items; the
  families; it has a model, `pre_model`): `out5_steps`, with the `<out>` list `#ostream(1) "off" #buffer("") 5` the rule `stdoutBufferInt`
  steps to `#ostream(1) "off" #buffer("5")`.
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
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

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

/-! ## `consistent`, and a stream rule's step (C7 form (a)) -/

/-- The text sentences of Γ's equations, in `fnItems`'s order (`TiePair.fnTextOf`): `append`'s two
are the module KSEQ's (sentences 1 and 2), the others the user module's. -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c kore.axiomDecls

theorem fnText_index : fnText.map (·.index) = [2976, 1, 2, 2925, 2933, 2932, 2931, 2930, 2937, 2936, 2943, 2942, 2935,
    2934, 2898, 2897, 2924, 2923, 2902, 2901, 2947, 2946, 2912, 2911, 2914, 2913, 2916, 2915, 2918, 2917, 2945, 2944,
    2908, 2907, 2910, 2909, 2949, 2948, 2953, 2952, 2951, 2950, 2927, 2926, 2929, 2928, 2920, 2919, 2922, 2921, 2939,
    2938, 2941, 2940, 2904, 2903, 2906, 2905, 2900, 2899] := by
  decide +kernel

/-- The function equations as written. -/
noncomputable def textPats : List P := fnText.map (trS · |>.pat)

/-- **Each of Γ's equations is the translation of its text sentence** (kernel). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

def callOrder : List Nat := []

theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel
theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel

/-- None named, and the semantics is `plain`; none of the ten parameter symbols (the seven
K-REFLECTION ones among them) is claimed total. -/
theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder [] :=
  FnObligations.of_nil
    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)
    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)
    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)
    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)

theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl_nil H)

/-- **Γ with the step's closure has a model, for every H** (C14 closure (a)). -/
theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)

/-- **The premises of the derivations**: every function equation as written, Γ's rule items (each
a consequence of its stream rule's sentence, `rules_from_text`), and the families. -/
noncomputable abbrev Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) textPats

/-- **`Pre` with the step's closure has a model, for every H.** -/
theorem pre_model (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Pre H ∪ Γstep (cH H)) :=
  TiePair.pre_model (shapeH H) (consistent H)

theorem readsConfined_c : c.readsConfined = false := by decide +kernel
theorem hrcH (H : HookParams) : (cH H).readsConfined = false := (Semantics.readsConfined_withHooks c H).trans readsConfined_c

def tCell : Sym := 390
def kCell : Sym := 393
def inCell : Sym := 395
def outCell : Sym := 397
def bufferL : Sym := 147
def ostreamL : Sym := 150
def stream : Srt := 16

theorem names : c.symName tCell = "Lbl'-LT-'t'-GT-'" ∧ c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧
    c.symName inCell = "Lbl'-LT-'in'-GT-'" ∧ c.symName outCell = "Lbl'-LT-'out'-GT-'" ∧
    c.symName bufferL = "Lbl'Hash'buffer'LParUndsRParUnds'K-IO'Unds'Stream'Unds'K" ∧
    c.symName ostreamL = "Lbl'Hash'ostream'LParUndsRParUnds'K-IO'Unds'Stream'Unds'Int" ∧
    c.sortName stream = "Stream" ∧ c.sortName Srt.list = "List" ∧ c.sortName Srt.string = "String" := by
  decide +kernel

private theorem hready : CExec.execReady c = true := by decide +kernel
theorem hreadyH (H : HookParams) : CExec.execReady (cH H) = true := (CExec.execReady_withHooks c H).trans hready

def sstr (x : String) : GroundTerm := .dv Srt.string (.tok x)

/-- `#buffer(s)`, as a list element. -/
def buf (x : String) : GroundTerm :=
  .inj stream Srt.kitem (.ctor bufferL [.ctor kseq [.inj Srt.string Srt.kitem (sstr x), .ctor dotk []]])

/-- The `<out>` cell's list: `#ostream(1)`, `"off"`, then `tail`. -/
def outL (tail : List GroundTerm) : GroundTerm :=
  .list Srt.list ([.inj stream Srt.kitem (.ctor ostreamL [int 1]), .inj Srt.string Srt.kitem (sstr "off")] ++ tail)

/-- The configuration with an empty k cell, an empty `<in>` and the `<out>` cell `out`. -/
def cfg (out : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor tCell [.ctor kCell [.ctor dotk []], .ctor inCell [.list Srt.list []], .ctor outCell [out]],
    .ctor counterLabel [int 0]]

def Out5 : Config c := ⟨cfg (outL [buf "", .inj Srt.int Srt.kitem (int 5)]), by decide +kernel⟩
def Buf5 : Config c := ⟨cfg (outL [buf "5"]), by decide +kernel⟩

-- The executable step at `Out5` reads no interpretation of the parameters: the rules
-- that apply call `Int2String` and `+String`, hooks of the registry.
kernel_rfl out5_withHooks : ∀ H : HookParams,
  CExec.successorsN (cH H) 50 Out5.val = CExec.successorsN c 50 Out5.val
/-- The step of `STDOUT-STREAM.stdoutBufferInt`, for every H: the executable step lists it. -/
theorem out5_step (H : HookParams) : Step (cH H) (TieRuleLhs.cfgH noRaw Out5 H) (TieRuleLhs.cfgH noRaw Buf5 H) := by
  have hy : Buf5.val ∈ CExec.successorsN (cH H) 50 Out5.val := by rw [out5_withHooks]; decide +kernel
  obtain ⟨_, hs⟩ := CExec.successorsN_step_ready (hreadyH H) (x := TieRuleLhs.cfgH noRaw Out5 H) hy
  exact hs

/-- **A stream rule's step, derived from `Pre`**, for every H: with the `<out>` list
`#ostream(1) "off" #buffer("") 5`, the rule `stdoutBufferInt` (priority 25) moves 5 into the buffer,
`#ostream(1) "off" #buffer("5")`. -/
theorem out5_steps (H : HookParams) : Pre H ⊧ (den (cH H) Out5.val ⇒ KoreAML.sNext (den (cH H) Buf5.val)) :=
  TiePair.cut (shapeH H) (sound_at_step _ (coreOKH H) (hrcH H) _ _ (out5_step H))

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
#print axioms KCore.NoteStream.shape
#print axioms KCore.NoteStream.consistent
#print axioms KCore.NoteStream.pre_model
#print axioms KCore.NoteStream.out5_steps
