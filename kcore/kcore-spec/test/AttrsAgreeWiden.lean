/-
  What `attrsAgree` accepts, against stricter variants of its parts stated here. Run from the
  package root:
  `lake env lean test/AttrsAgreeWiden.lean`.
  A `simplification` sentence is no equation of the symbol at its head (`AttrsAgree.eqnsOf`):
  - `eqnsOf` is `formerEqnsOf` (the equations at the head, less the law sentences) less the
    sentences carrying `simplification` (`eqnsOf_eq_former`);
  - `prios` is the comparison over `formerEqnsOf` less those sentences (`prios_eq_former`);
  - `fns` and `hooks` read the list only as "the text states no equation of n", so they hold
    wherever the variants over `formerEqnsOf` hold (`fns_of_former`, `hooks_of_former`).
  On `hw-simp-owise` and `hw-simp-priority` (the one equation of `half` carries `simplification`,
  so `half` is a parameter without implementation) the five parts are true.
  A function of the semantics may be declared with a `hook` attribute that names no registry hook:
  - `fns` holds wherever the variant that asks a function to be declared without `hook` holds
    (`fns_of_hookless`), and wherever the one over `formerEqnsOf` does (`fns_of_former`);
  - on `f2-examples/ens.kompile.kore` with `half` declared `hooked-symbol … hook{}("INT.rand")`,
    a hook the registry does not have, `half` is a function with its equation and the five parts
    are true.
  An instance of a sort-parametric declaration that the semantics has is compared at its own name
  with the declaration's attributes (`AttrsAgree.symDeclsAt`, `instDecls`):
  - where the semantics names no instance (no own name ends with a brace) the rows are the text's
    declarations (`symDeclsAt_eq_symDecls`), and the three statements above are stated there
    (their hypothesis `instDecls k c = []`); an instance adds its own row;
  - on `parsel` the instances' rows are `sel{K}` and `sel{Int}`, each with the declaration's
    `function{}`, and a tie's pairing finds the two equations of `sel{K}` by its instance name
    (`TiePair.findEqn`, `AttrsAgree.eqnHeadIs`).
-/
import KcoreSpec

set_option autoImplicit false

open KCore AttrsAgree

/-- The axioms with `n` at the head of their left side that are no law sentence, the
`simplification` sentences among them. -/
def formerEqnsOf (k : Kore.Definition) (n : String) : List Kore.Axiom :=
  (k.axiomDecls.map (·.ax)).filter fun a => eqnHeadIs n a.pattern && !isLaw a

theorem eqnsOf_eq_former (k : Kore.Definition) (n : String) :
    eqnsOf k n = (formerEqnsOf k n).filter (!has ·.attributes "simplification") := by
  simp only [eqnsOf, formerEqnsOf, List.filter_filter]
  congr 1; funext a; exact Bool.and_comm _ _

theorem prios_eq_former (k : Kore.Definition) (d : Definition) : prios k d =
    (let c := d.sem
     let axs := k.axiomDecls.map (·.ax)
     d.pres.rules.length == c.rules.length &&
     ((c.rules.zip d.pres.rules).all fun (r, rp) => rewritePrioOf k rp.info.uid == some r.prio) &&
     ((axs.filter (isRewrite ·.pattern)).all fun a => d.pres.rules.any fun rp => uidOf a.attributes == some rp.info.uid) &&
     c.allFns.all fun f =>
       (((formerEqnsOf k (c.symName f.label)).filter (!has ·.attributes "simplification")).map
           (prioOf ·.attributes)).isPerm (f.clauses.map (·.prio))) := by
  simp only [prios, eqnsOf_eq_former]

theorem eqnsOf_isEmpty_of_former {k : Kore.Definition} {n : String}
    (h : (formerEqnsOf k n).isEmpty = true) : (eqnsOf k n).isEmpty = true := by
  rw [List.isEmpty_iff] at h
  rw [eqnsOf_eq_former, h]; rfl

/-- `fns`'s comparison at the text's declarations, with `formerEqnsOf` in "the text states no
equation of n" and a function of the semantics declared without `hook`. -/
def formerFns (k : Kore.Definition) (c : Semantics) : Bool :=
  (symDecls k).all fun (n, as) =>
    let fn := has as "function" && !has as "hook"
    let isFn := c.allFns.any (c.symName ·.label == n)
    let own := (c.ctorSigs ++ c.params.map (·.sig) ++ c.ovlSigs).any (c.symName ·.name == n)
    let par := !(c.ctorSigs ++ c.ovlSigs).any (c.symName ·.name == n) &&
      (c.params.all fun p => c.symName p.sig.name != n || (p.impl.isNone && !p.raw)) && (formerEqnsOf k n).isEmpty
    (!isFn || fn) && (!(fn && own) || isFn || par)

/-- `hooks`'s comparison at the text's declarations, with `formerEqnsOf` in "the text states no
equation of n". -/
def formerHooks (k : Kore.Definition) (c : Semantics) : Bool :=
  (symDecls k).all (fun (n, as) =>
    match strArg as "hook" with
    | some h =>
      (hookSigs.all fun g => c.symName g.name != n || regHookOf h == some g.name) &&
      (c.params.all fun p => c.symName p.sig.name != n || p.impl == regHookOf h)
    | none =>
      (hookSigs.all fun g => c.symName g.name != n || (libFn g && has as "function")) &&
      c.params.all fun p => c.symName p.sig.name != n ||
        (p.impl.isNone && (p.raw != has as "function") && (formerEqnsOf k n).isEmpty))

/-- `fns`'s comparison at the text's declarations, with a function of the semantics declared
without `hook`. -/
def fnsHookless (k : Kore.Definition) (c : Semantics) : Bool :=
  (symDecls k).all fun (n, as) =>
    let fn := has as "function" && !has as "hook"
    let isFn := c.allFns.any (c.symName ·.label == n)
    let own := (c.ctorSigs ++ c.params.map (·.sig) ++ c.ovlSigs).any (c.symName ·.name == n)
    let par := !(c.ctorSigs ++ c.ovlSigs).any (c.symName ·.name == n) &&
      (c.params.all fun p => c.symName p.sig.name != n || (p.impl.isNone && !p.raw)) && (eqnsOf k n).isEmpty
    (!isFn || fn) && (!(fn && own) || isFn || par)

theorem fnRow_mono (i f hk u y z p a b : Bool) (e : a = true → b = true)
    (h : ((!i || (f && !hk)) && (y || z || (p && a))) = true) :
    ((!i || (f && (!hk || u))) && (y || z || (p && b))) = true := by
  revert e h
  cases a <;> cases b <;> cases i <;> cases f <;> cases hk <;> cases u <;> cases y <;> cases z <;>
    cases p <;> decide

theorem fns_of_hookless {k : Kore.Definition} {c : Semantics} (hI : instDecls k c = [])
    (h : fnsHookless k c = true) : fns k c = true := by
  simp only [fnsHookless, fns, symDeclsAt, hI, List.append_nil, List.all_eq_true] at h ⊢
  rintro ⟨n, as⟩ hx
  exact fnRow_mono _ _ _ _ _ _ _ _ _ id (h (n, as) hx)

theorem fns_of_former {k : Kore.Definition} {c : Semantics} (hI : instDecls k c = [])
    (h : formerFns k c = true) : fns k c = true := by
  simp only [formerFns, fns, symDeclsAt, hI, List.append_nil, List.all_eq_true] at h ⊢
  rintro ⟨n, as⟩ hx
  exact fnRow_mono _ _ _ _ _ _ _ _ _ (@eqnsOf_isEmpty_of_former k n) (h (n, as) hx)

theorem hooks_of_former {k : Kore.Definition} {c : Semantics} (hI : instDecls k c = [])
    (h : formerHooks k c = true) : hooks k c = true := by
  simp only [formerHooks, hooks, symDeclsAt, hI, List.append_nil, List.all_eq_true] at h ⊢
  intro x hx
  have hx' := h x hx
  rcases x with ⟨n, as⟩
  have e := @eqnsOf_isEmpty_of_former k n
  revert hx'
  cases strArg as "hook" with
  | some hk => exact id
  | none =>
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true]
    exact fun ⟨h1, h2⟩ => ⟨h1, fun p hp => (h2 p hp).imp_right fun ⟨h3, h4⟩ => ⟨h3, e h4⟩⟩

/-- The five parts of `attrsAgree` on the reading of the text at `path` (edited by `edit`). -/
def attrsParts (path : String) (edit : String → String := id) : IO String := do
  match Kore.parseDefinition (edit (← IO.FS.readFile path)) with
  | .error e => return s!"KORE read error {e}"
  | .ok k =>
    return match Parse.parse k with
      | .ok d =>
        let ps := d.sem.params.filter fun p => p.impl.isNone
        s!"{[ctors k d.sem, fns k d.sem, hooks k d.sem, colls k d.sem, prios k d]}; fns {d.sem.fns.map fun f => (d.sem.symName f.label, f.clauses.length)}; params without impl {ps.map fun p => (d.sem.symName p.sig.name, p.raw)}"
      | .error r => s!"{r.reason.name} {r.detail}"

/--
info: [true, true, true, true, true]; fns []; params without impl [(Lblhalf, false)]
[true, true, true, true, true]; fns []; params without impl [(Lblhalf, false)]
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← attrsParts "test/constructs/fixtures/hw-simp-owise/hw-simp-owise.kore")
  IO.println (← attrsParts "test/constructs/fixtures/hw-simp-priority/hw-simp-priority.kore")

/--
info: [true, true, true, true, true]; fns [(Lblhalf, 1)]; params without impl []
-/
#guard_msgs in
#eval show IO Unit from do
  IO.println (← attrsParts "f2-examples/ens.kompile.kore" fun s =>
    s.replace "  symbol Lblhalf{}(SortInt{}) : SortInt{} [function{}(), "
      "  hooked-symbol Lblhalf{}(SortInt{}) : SortInt{} [function{}(), hook{}(\"INT.rand\"), ")

/-- No own name of the semantics ends with a closing brace: it names no instance. -/
theorem instDecls_eq_nil {k : Kore.Definition} {c : Semantics}
    (h : ∀ m ∈ c.symNames, instBase m = none) : instDecls k c = [] := by
  unfold instDecls
  split
  · rfl
  · rw [List.filterMap_eq_nil_iff]
    intro m hm; rw [h m hm]; rfl

theorem symDeclsAt_eq_symDecls {k : Kore.Definition} {c : Semantics}
    (h : ∀ m ∈ c.symNames, instBase m = none) : symDeclsAt k c = symDecls k := by
  rw [symDeclsAt, instDecls_eq_nil h, List.append_nil]

/-- The kernel reduces an instance's declared name at a literal. -/
example : instBase "Lblsel{K,Int}" = some "Lblsel" ∧ instBase "Lblsel" = none ∧
    instBase "Lbl'Unds'andBool'Unds'" = none := by decide +kernel

/--
info: instances [(Lblsel{K}, true), (Lblsel{Int}, true)]; instance clause keys [(Lblsel{K}, 50), (Lblsel{K}, 50)]; found [true, true]
-/
#guard_msgs in
#eval show IO Unit from do
  match Kore.parseDefinition (← IO.FS.readFile "f2-examples/parsel.kompile.kore") with
  | .error e => IO.println s!"KORE read error {e}"
  | .ok k =>
    match Parse.parse k with
    | .error r => IO.println s!"{r.reason.name} {r.detail}"
    | .ok d =>
      let keys := (TiePair.clauseKeys d.sem).filter fun key => (instBase key.1).isSome
      IO.println s!"instances {(instDecls k d.sem).map fun (n, as) => (n, has as "function")}; instance clause keys {keys}; found {keys.map fun key => (TiePair.findEqn k.axiomDecls key).isSome}"
