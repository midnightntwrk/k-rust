/-
  K-REFLECTION's `#configuration`, read from K 7.1.337 kompile's KORE. Run from the package root:
  `lake env lean test/Configuration.lean`.

  `f2-examples/e6cfg.kompile.kore` (`e6cfg.k`, the construct fixture e6-configuration):
  `rule <k> go => wrap(#configuration) ... </k>` with K-IO and K-REFLECTION imported and no other rule. The
  declaration `hooked-symbol Lbl'Hash'configuration'Unds'K-REFLECTION'Unds'K{}() : SortK{}
  [function{}(), hook{}("KREFLECTION.configuration"), impure{}()]` is read as the definition's own
  (`reflectionAsOwn`): a parameter symbol, which the text declares a function and of which it states
  nothing else, so every theorem holds for each interpretation of it. No interpretation is the one
  K's documentation gives it (the configuration the term is evaluated in), since a parameter's value
  is fixed for every configuration. Nothing is refused or unaccounted, and `coreOK` holds (decided by
  the compiled `coreOK`, not in the kernel).

  At `HookParams.none` the parameter has no value, so the rule's right side has none, and the
  configuration `go` has no successor.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

/-- The reader's verdict on the text at `path`: its sentences read in another form than written or
not read, the number of read sentences applying `#configuration` (the account's line, read at a
fixed value, not the documented one: `Parse.configurationUses`), and the refusal or what the account
finds. -/
def verdict (path : String) : IO String := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    let cls := (Parse.classCounts k).filter fun (n, _) => n.startsWith "read " || n.startsWith "unread "
    let cls := cls.mergeSort fun a b => decide (a.1 ≤ b.1)
    let uses := ((Parse.configurationUses k).getD []).length
    return s!"{cls}; sentences applying #configuration {uses}; " ++ match Parse.parse k with
      | .ok d => s!"read; unaccounted {(Parse.unconsumed k d).map (·.detail)}; uninduced {(Parse.uninduced k d).length}; missing {(Parse.missingBuiltin k d).map (·.head)}; coreOK {d.sem.coreOK}"
      | .error r => s!"{r.reason.name}{if r.detail.isEmpty then "" else " " ++ r.detail}"

/--
info: [(read reflectionAsOwn, 8), (unread parametricUnused, 1), (unread setIdempotence, 1)]; sentences applying #configuration 1; read; unaccounted []; uninduced 0; missing []; coreOK true
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← verdict "f2-examples/e6cfg.kompile.kore")

namespace Configuration

definition_of defn from "f2-examples/e6cfg.kompile.kore"

/-- The semantics at the interpretation that gives every parameter no value. -/
noncomputable abbrev c : Semantics := defn.sem.withHooks HookParams.none

def kCell : Sym := 379
def cfgSym : Sym := 385
def go : Sym := 382
def wrap : Sym := 383
def expS : Srt := 32

theorem names_ok : c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧
    c.symName cfgSym = "Lbl'Hash'configuration'Unds'K-REFLECTION'Unds'K" ∧
    c.symName go = "Lblgo" ∧ c.symName wrap = "Lblwrap" ∧ c.sortName expS = "Exp" := by
  decide +kernel

/-- `#configuration` is a parameter symbol of the definition; the one rule is `go`'s. -/
theorem configuration_param : c.params.any (·.sig.name == cfgSym) = true ∧ c.rules.length = 1 := by
  decide +kernel

theorem ok : c.ok = true := by decide +kernel
theorem srReady : c.srReady = true := by decide +kernel
theorem matchReady : c.matchReady = true := by decide +kernel
theorem coherent : CoherentAll c :=
  Det.coherentAll_of_nil ok srReady matchReady (by decide +kernel) (by decide +kernel)

def cfg (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj expS Srt.kitem st, .ctor dotk []]],
    .ctor counterLabel [.dv Srt.int (.int 0)]]

def Go : Config c := ⟨cfg (.ctor go []), by decide +kernel⟩

/-- The rule's right side, `<k> wrap(#configuration) ~> K </k>` beside the counter variable. -/
def rhs : Term :=
  .app topLabel [.app kCell [.app kseq [.inj expS Srt.kitem (.app wrap [.app cfgSym []]), .var 0]], .var 1]

theorem rules_rhs : c.rules.map (fun r => Term.beq r.rhs rhs) = [true] := by decide +kernel

/-- The executable checks never read a parameter's interpretation (`Cert.stuckCheck_withHooks`), so
no certificate decides this point; the right side's result is derived instead. At `HookParams.none`
`#configuration` has no value (`paramVal` is the interpretation's, which gives none), and each
constructor above it is strict. -/
theorem rhs_none (σ : Subst) : EvalTerm c σ rhs none := by
  have hp : EvalTerm c σ (.app cfgSym []) none :=
    .param (by decide +kernel) (by decide +kernel) (by decide +kernel) .nil
      (by show none = c.paramVal cfgSym []; decide +kernel)
  have hw : EvalTerm c σ (.app wrap [.app cfgSym []]) none := .ctor (by decide +kernel) (.cons hp .nil)
  have hk : EvalTerm c σ (.app kseq [.inj expS Srt.kitem (.app wrap [.app cfgSym []]), .var 0]) none :=
    .ctor (by decide +kernel) (.cons (.inj hw) (.cons .var .nil))
  have hc : EvalTerm c σ (.app kCell [.app kseq [.inj expS Srt.kitem (.app wrap [.app cfgSym []]), .var 0]])
      none := .ctor (by decide +kernel) (.cons hk .nil)
  exact .ctor (by decide +kernel) (.cons hc (.cons .var .nil))

/-- At `HookParams.none`, `#configuration` has no value, so the rule's right side has none and `go`
has no successor. -/
theorem stuck_go : ∀ y, ¬ Step c Go y := by
  intro y h
  cases h with
  | rule r mem σ _ _ _ _ heval _ _ _ =>
    have hr : r.rhs = rhs := by
      have := List.mem_map_of_mem (f := fun r => Term.beq r.rhs rhs) mem
      rw [rules_rhs] at this
      exact Det.Term.beq_sound (List.mem_singleton.mp this)
    rw [hr] at heval
    cases EvalTerm.functional coherent heval (rhs_none σ)

end Configuration
