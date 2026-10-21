import {
  compileBackendNative,
  compileDefinitionNative,
  createBackendNative,
  formatKoreDefinitionNative,
  parseKastNative,
  parseKoreNative,
  parseProgramNative,
  printKastNative,
  printKoreNative,
  runFuzzCampaignNative,
  type NativeBackend,
  type NativeDiagnostic,
  type NativeCompileDefinitionOptions,
  type NativeFuzzDefinition,
  type NativeParseProgramOptions,
} from '../native.js'

export interface KastSort {
  node: 'KSort'
  name: string
  params: KastSort[]
}

export interface KastLabel {
  node: 'KLabel'
  name: string
  params: KastSort[]
}

export type KastTerm =
  | { node: 'KToken'; sort: KastSort; token: string }
  | { node: 'KApply'; label: KastLabel; arity: number; args: KastTerm[] }
  | { node: 'KSequence'; arity: number; items: KastTerm[] }
  | { node: 'KVariable'; name: string; sort?: KastSort }
  | { node: 'KRewrite'; lhs: KastTerm; rhs: KastTerm }
  | { node: 'KAs'; pattern: KastTerm; alias: KastTerm }
  | { node: 'InjectedKLabel'; label: KastLabel }

export interface Kast {
  format: 'KAST'
  version: 4
  term: KastTerm
}

export type KoreSort =
  | { tag: 'SortVar'; name: string }
  | { tag: 'SortApp'; name: string; args: KoreSort[] }

export type KorePattern =
  | { tag: 'String'; value: string }
  | { tag: 'EVar' | 'SVar'; name: string; sort: KoreSort }
  | { tag: 'App'; name: string; sorts: KoreSort[]; args: KorePattern[] }
  | { tag: 'Top' | 'Bottom'; sort: KoreSort }
  | { tag: 'And' | 'Or'; sort: KoreSort; patterns: KorePattern[] }
  | { tag: 'Not'; sort: KoreSort; arg: KorePattern }
  | { tag: 'Next'; sort: KoreSort; dest: KorePattern }
  | { tag: 'Implies' | 'Iff'; sort: KoreSort; first: KorePattern; second: KorePattern }
  | { tag: 'Rewrites'; sort: KoreSort; source: KorePattern; dest: KorePattern }
  | {
      tag: 'Exists' | 'Forall'
      sort: KoreSort
      var: string
      varSort: KoreSort
      arg: KorePattern
    }
  | { tag: 'Mu' | 'Nu'; var: string; varSort: KoreSort; arg: KorePattern }
  | { tag: 'Ceil' | 'Floor'; argSort: KoreSort; sort: KoreSort; arg: KorePattern }
  | {
      tag: 'Equals' | 'In'
      argSort: KoreSort
      sort: KoreSort
      first: KorePattern
      second: KorePattern
    }
  | { tag: 'DV'; sort: KoreSort; value: string }
  | { tag: 'LeftAssoc' | 'RightAssoc'; symbol: string; sorts: KoreSort[]; argss: KorePattern[] }

export interface Kore {
  format: 'KORE'
  version: 1
  term: KorePattern
}

export interface Source {
  /** Stable virtual filename used for `requires` resolution and diagnostics. */
  name: string
  text: string
}

export interface ParseProgramOptions {
  definition: string
  moduleName: string
  sort: string
  program: string
  sourceName?: string
  /** Additional virtual files keyed by the names used in `requires`. */
  sources?: Readonly<Record<string, string>> | readonly Source[]
  markdownSelector?: string
  /** Load k-rust's embedded standard prelude. Defaults to true. */
  includePrelude?: boolean
}

export type CompilationBackend = 'rust' | 'llvm'

export interface CompileDefinitionOptions {
  definition: string
  moduleName: string
  backend?: CompilationBackend
  sourceName?: string
  /** Additional virtual files keyed by the names used in `requires`. */
  sources?: Readonly<Record<string, string>> | readonly Source[]
  markdownSelector?: string
  /** Load k-rust's embedded standard prelude. Defaults to true. */
  includePrelude?: boolean
  /** Pretty-printer line width. Defaults to 100. */
  koreWidth?: number
}

export interface Diagnostic extends NativeDiagnostic {
  severity: 'error' | 'warning'
  inputAddresses: InputAddress[]
}

export interface InputAddress {
  input: 'structured' | 'compile'
  module: string
  index: number
}

export interface ParsedProgram {
  text: string
  kast: Kast
  diagnostics: Diagnostic[]
}

export interface CompiledDefinition {
  definitionKore: string
  syntaxDefinitionKore: string
  macrosKore: string
  diagnostics: Diagnostic[]
}

export interface SerializedKast {
  text: string
  kast: Kast
}

export interface SerializedKore {
  text: string
  kore: Kore
}

/** One axiom sentence: where its author wrote it, when it says so, and its place in the KORE definition, which no other sentence shares. */
export interface RuleOrigin {
  source: string | null
  location: string | null
  /** Omitted for a sentence the backend read on its own rather than from its definition. */
  sentence?: RuleSentence
}

/** The declaring module and the sentence's zero-based index among all of that module's sentences, whatever their kind. */
export interface RuleSentence {
  module: string
  index: number
}

/** An application of a symbol declared total (or functional) that one of its equations reduced to bottom. */
export interface ContradictedTotal {
  /** KORE name of the symbol whose attribute is contradicted. */
  symbol: string
  /** The K label that KORE name encodes (e.g. 'tDiv(_)_M_Int_Int'), as the CLI prints it. */
  kLabel?: string
  /** The equation's compiled id, as in ruleCatalog. */
  ruleId: string
  ruleLabel?: string
  /** Where the equation is written, when the KORE carries it. */
  origin?: RuleOrigin
  /** The application the equation rewrote. */
  application: Kore
  /** The undefined term the equation's result reached. */
  undefined: Kore
}

/** One compiled axiom, after equivalent written axioms have been combined. */
export interface CompiledRule {
  id: string
  kind: 'rewrite' | 'function-equation' | 'simplification' | 'definedness'
  executable: boolean
  label: string | null
  priority: number
  origins: RuleOrigin[]
  sharedIdentity: boolean
}

export interface BackendCapabilities {
  execution: boolean
  simplification: boolean
  implication: boolean
  modelGeneration: boolean
  proving: boolean
  moduleAddition: boolean
  smt: boolean
  stepTimeouts: boolean
  search: boolean
  observation: boolean
  /** `execute` and `executeObserved` accept `collectCoverage`. */
  coverage: boolean
  /** `execute` and `executeObserved` accept `collectOffered` beside `collectCoverage`. */
  coverageOffered: boolean
  /** `execute` and `executeObserved` report `stackStops`. */
  stackStops: boolean
  /** `execute` and `executeObserved` report `smtUnknowns`. */
  smtUnknowns: boolean
  /** `execute`, `executeObserved` and every search mark leaves, states, witnesses and matches with 'implementation-chosen-value' and report `implementationChosenValues`. */
  implementationChosenValues: boolean
  /** `execute`, `executeObserved` and every search mark leaves, states, witnesses and matches with 'contradicted-claim' and report `contradictedClaims`. */
  contradictedClaims: boolean
  /** `execute`, `executeObserved` and every search report `allowanceRefusals`. */
  allowanceRefusals: boolean
  /** `execute`, `executeObserved` and every search report `unsupportedHooks`. */
  unsupportedHooks: boolean
}

export interface CreateBackendOptions {
  definitionKore: string
  moduleName: string
  smtTimeoutMs?: number
  smtRetryLimit?: number
}

export type ExecutionStrategy = 'all' | 'any'

export interface ExecuteOptions {
  state: Kore
  moduleName?: string
  maxDepth?: number
  maxBreadth?: number
  maxSimplificationIterations?: number
  strategy?: ExecutionStrategy
  stopAtBranch?: boolean
  cutPointRules?: string[]
  terminalRules?: string[]
  stepTimeoutMs?: number
  movingAverageTimeout?: boolean
  assumeStateDefined?: boolean
  /**
   * `state-set` (default) merges structurally equal final configurations into one leaf;
   * `path-set` returns one leaf per explored path, each with its own trace, branch and
   * observations.
   */
  resultModality?: 'state-set' | 'path-set'
  /**
   * Report the run's coverage as `ExecutionResult.coverage`: the rules and equations it applied,
   * and those whose condition it began to decide (docs/compatibility.md, "Run coverage").
   */
  collectCoverage?: boolean
  /**
   * With `collectCoverage`, also report `RunCoverage.offered`: the rules and equations whose
   * left-hand side matched a subject the run selected them as candidates for, tried there or
   * not. A request that sets it without `collectCoverage` is refused. A candidate never tried
   * costs one match at every visit of its site while it has not matched (docs/compatibility.md,
   * "Run coverage").
   */
  collectOffered?: boolean
  /**
   * The most states the run may visit across all its paths; absent: no bound. A run that
   * reaches it ends with one 'work-bound' leaf for the state it did not visit, the last leaf,
   * and does not explore the other pending states (docs/compatibility.md, "Work budget").
   */
  maxWork?: number
  /**
   * Whether each leaf carries its path's `trace` (default `true`). With `false` every leaf's
   * `trace` is empty and every other field is unchanged, so the traces no longer grow with the
   * total path length. An observed run's `branch` and `observations` stay proportional to each
   * leaf's depth, so only an unobserved branching run's output is then linear in its leaves.
   */
  trace?: boolean
  /**
   * What the request answers when a cancellation ends its run: 'partial' (the default) returns the
   * leaves finished before it and the stopped state as a 'cancelled' leaf; 'error' fails with the
   * cancellation and builds no leaf beyond the stopped state's own. This host cannot cancel a
   * request, so the field changes nothing here (a failed solver prelude is an error under both);
   * it is accepted for parity with the wire protocol, where an embedder that cancels (the Rust
   * `CancellationToken`) gets the error shape.
   */
  cancelledResult?: 'partial' | 'error'
  schemaVersion?: number
}

export interface BackendTraceEntry {
  depth: number
  kind: 'simplification' | 'rewrite' | 'claim' | 'remainder'
  label?: string
  uniqueId: string
}

export interface ExecutionLeaf {
  state: Kore
  diagnostics?: BackendDiagnostic[]
  /** Present on branch and cut-point halts. */
  candidates?: ExecutionCandidate[]
  /** The branch's remaining path candidate, when one remains. */
  remainder?: ExecutionRemainder
  depth: number
  /**
   * 'trivial' is an undefined step: under the state's constraint some rule applies to every
   * instance and, under strategy 'all', none has a defined successor (under 'any', none from a
   * rule of that priority through the collection candidate the step follows); the constraint is
   * not checked for satisfiability.
   * 'work-bound': the request's `maxWork` was reached before this state was visited; the state is
   * where exploration stopped, unexpanded and unnormalised, not a result, and the pending states
   * were not explored.
   * Under strategy 'all' without stops, bounds or diagnostics, the leaves' constraints cover the initial state.
   */
  reason:
    | 'cancelled'
    | 'stuck'
    | 'trivial'
    | 'vacuous'
    | 'branch'
    | 'cut-point'
    | 'terminal'
    | 'depth-bound'
    | 'breadth-bound'
    | 'work-bound'
    | 'indeterminate'
    | 'unsupported-hook'
    | 'simplification-error'
    | 'timeout'
  /** Rule responsible for a 'trivial' leaf, when its halt names one. */
  ruleId?: string
  /** Optional label of that rule, as in rule catalog and observations. */
  ruleLabel?: string
  /**
   * Present on a 'trivial' or 'vacuous' leaf whose emptiness comes from an equation of a symbol
   * declared total (or functional) that reduced an application of it to bottom: the definition
   * contradicts the attribute on that input. Diagnostic only; reason and state are unaffected.
   */
  contradictedTotal?: ContradictedTotal
  /** The stopped step's cause: for an indeterminate halt, and `{ kind: 'stack-exhausted' }` for a 'simplification-error' leaf whose state ran out of stack; same encoding as search's failures. */
  cause?: SearchFailure
  /** Legacy human-readable context only; use cause, candidates and remainder for halt evidence. */
  detail?: string
  trace: BackendTraceEntry[]
  /** Filter-independent transition identities; absent in unobserved execution. */
  branch?: TransitionId[]
  /** Ordered effects committed on this branch, independent of observation. */
  effects?: BackendEffect[]
  observations?: ObservationEvent[]
}

export interface ExecutionCandidate {
  state: Kore
  uniqueId: string
  label?: string
  diagnostics?: BackendDiagnostic[]
}

export interface ExecutionRemainder {
  state: Kore
  ruleIds: string[]
  diagnostics?: BackendDiagnostic[]
}

export interface ExecutionResult {
  /** The reading of `leaves` selected by `ExecuteOptions.resultModality`. */
  modality: 'state-set' | 'path-set'
  leaves: ExecutionLeaf[]
  /** Compatibility copy of effects when execution retains exactly one leaf. */
  effects: BackendEffect[]
  discarded?: UncommittedObservation[]
  /** The states the run visited across all its paths, the unit `maxWork` bounds. */
  work: number
  /**
   * The visited states whose rewrite step ran and answered, whatever the answer (successors,
   * a branch or cut-point report, or a verdict that ends the state such as stuck or trivial);
   * at most `work`, and deterministic exactly where `work` is (docs/compatibility.md,
   * "Work budget").
   */
  expanded: number
  /** Present exactly when the request set `collectCoverage`. */
  coverage?: RunCoverage
  /**
   * The stops for lack of native stack the run met, those that ended a state and those met while
   * a result was only refined; absent when none. A run that reports any is outside the
   * determinism contract (docs/compatibility.md, "Determinism and concurrency").
   */
  stackStops?: number
  /**
   * The undecided answers (`unknown`: a timeout, the solver's resource limit or its
   * incompleteness) the solver delivered to the run's decisions, each counted once after
   * retries; absent when none, and always absent without a solver. A run that reports none took
   * every decision from a decided answer, so within the determinism contract it gives one result
   * on a fresh backend and on a reused one (docs/compatibility.md, "Determinism and
   * concurrency").
   */
  smtUnknowns?: number
  /**
   * Every distinct value the definition leaves open that the run read, in first-read order;
   * absent when none (docs/compatibility.md, "Implementation-chosen hook values"). It includes
   * the values read by work that ended on no reported leaf (a vanished candidate, a state a
   * `state-set` merge absorbed). When absent, every model of the definition that agrees with the
   * request's inputs and k-rust's stated readings gives the run the same leaves. In a run with
   * `maxWork` or `maxBreadth` every leaf carries every value listed here, and so does, under
   * `state-set`, every leaf a leaf of another halt class may stand for in the final merge (a
   * `depth-bound` or other unexplored or undecided leaf, and with `terminalRules` a `stuck` or
   * `terminal` one).
   */
  implementationChosenValues?: ChosenValue[]
  /**
   * Every distinct contradicted claim the run observed, and those the load of its definition
   * observed, in first-observed order; absent when none (docs/compatibility.md, "A contradicted
   * total attribute is named, not repaired"). It includes the records of work that ended on no
   * reported leaf (a candidate a defined sibling covered, a state a `state-set` merge absorbed).
   * It is complete for contradictions found by evaluation on ground arguments; a symbolic state
   * trusts the claim, so its absence says nothing about a non-ground run. Each record says who
   * observed it (`observedIn`): the load's records are facts about the definition, on this list
   * and on no leaf, and a contradiction the load and the run both observed is listed once for each.
   */
  contradictedClaims?: ContradictedClaim[]
  /**
   * Every distinct `Bytes` result the memory allowance refused in the run or in the load of its
   * definition, in first-met order, including a refusal inside work that was undone or passed
   * over, which leaves no diagnostic; absent when none. A result without it is the result under
   * every allowance of at least as many bytes (docs/compatibility.md, "Resource bounds").
   */
  allowanceRefusals?: UnevaluatedHook[]
  /**
   * Every distinct application left unevaluated as an unsupported hook, other than an allowance
   * refusal, in the run or in the load of its definition, in first-met order, whatever became of
   * the work that met it; absent when none.
   */
  unsupportedHooks?: UnevaluatedHook[]
}

/** A hook application a run left unevaluated, with the reason the 'unsupported-hook-unevaluated' diagnostic gives, and who met it. */
export interface UnevaluatedHook {
  hook: string
  reason: string
  observedIn: ObservedIn
}

/** Who observed a run-level record: the load of the definition (a fact about the definition, on the result's lists only) or the run that reports it. */
export type ObservedIn = 'load' | 'run'

/**
 * A claim of the definition an evaluation found contradicted by the definition's own equations,
 * one of two kinds told apart by `claim`:
 * - `claim: 'total'`: a symbol declared total (or functional) whose equation reduced an
 *   application to defined arguments to bottom, with the fields of `ContradictedTotal`;
 * - `claim: 'preserves-definedness'`: a rule declared so (`ruleId`, `ruleLabel`, `origin`) whose
 *   result term as the step built it (`application`; for a disjunctive right-hand side, every
 *   alternative's, of which the first is named) its normalization found bottom (`undefined`:
 *   where, a subterm of it or of a callee's equation result), with no `symbol` or `kLabel`.
 * The other fields are `ContradictedClaimFields`.
 */
export type ContradictedClaim =
  | ({ claim: 'total'; symbol: string; kLabel?: string } & ContradictedClaimFields)
  | ({ claim: 'preserves-definedness' } & ContradictedClaimFields)

/**
 * The fields of a `ContradictedClaim` of either kind. `rewriteRule*` name the rewrite rule whose
 * attempt or successor's normalization observed it, absent when no rule's work did. `ground`: the
 * application is variable-free and the work that refuted the claim depended on nothing that may
 * differ between models (it read no value the definition leaves open, among the other path facts,
 * and assumed nothing but true: for `total`, no constraint of the state; for
 * `preserves-definedness`, every constraint of the step simplified to true, so its `requires` was
 * decided), so the claim is false at that input in every model that agrees with the request's
 * inputs (on the I/O route, the console state too) and with k-rust's stated readings; a
 * non-ground record shows nothing. `observedIn`: whether the definition's
 * load or this run observed it; a leaf's records are always 'run'.
 */
export interface ContradictedClaimFields {
  ruleId: string
  ruleLabel?: string
  origin?: RuleOrigin
  application: Kore
  undefined: Kore
  rewriteRuleId?: string
  rewriteRuleLabel?: string
  rewriteRuleOrigin?: RuleOrigin
  ground: boolean
  observedIn: ObservedIn
}

/** A value the definition leaves open that a run read: the hook that computed it and what is open about it. */
export interface ChosenValue {
  hook: string
  class: ChosenClass
}

export type ChosenClass =
  | 'order'
  | 'item'
  | 'float-destination'
  | 'nan-sign'
  | 'letter-case'
  | 'signed-zero'
  | 'fresh-name'
  | 'read-count'
  | 'effect-order'

/**
 * The `UNIQUE_ID`s of the rules and equations a run used, each list sorted: `applied` those it
 * applied, `matched` those plus every one whose condition it began to decide for a matched
 * instance. Both cover every explored path, whatever the result modality.
 */
export interface RunCoverage {
  applied: string[]
  matched: string[]
  /**
   * Present exactly when the request set `collectOffered`: `matched` plus every rule and equation
   * whose left-hand side matched a subject the run selected it as a candidate for, whether or not
   * the run went on to decide its condition there.
   */
  offered?: string[]
}

export interface TransitionId {
  rule: string
  /** Lowercase SHA-256 of canonical compact successor KORE. */
  target: string
}

export interface BackendBinding {
  variable: Kore
  value: Kore
}

export interface BackendTermPair {
  left: Kore
  right: Kore
}

export type BackendEffect = { kind: 'user-log'; message: string }

/** The kind of committed transition. */
export type TransitionClass =
  | 'rewrite'
  | 'remainder'
  /** Reserved for a circularity or trusted claim applied inside an observable proof; no operation emits it yet. */
  | 'claim'

/** The kind of rule applied while normalizing a branch state. */
export type EvaluationClass = 'function-equation' | 'simplification' | 'builtin'

/** A committed transition; `id` is an element of the branch it is reported on, in order. */
export interface TransitionObservation {
  kind: 'transition'
  id: TransitionId
  class: TransitionClass
  ruleLabel?: string
  bindings: BackendBinding[]
  introducedPredicates: Kore[]
  before: Kore
  after: Kore
  /** Attributes committed branch effects to this observed transition. */
  effects: BackendEffect[]
}

/**
 * An equation, simplification, or builtin application that normalized a state of the branch.
 * `anchor` is the number of branch entries preceding it: the normalized state is the one reached
 * by the first `anchor` transitions (the initial state when 0). Diagnostic only: presence,
 * multiplicity, and order depend on the simplifier's strategy.
 */
export interface EvaluationObservation {
  kind: 'evaluation'
  rule: string
  class: EvaluationClass
  ruleLabel?: string
  anchor: number
  before: Kore
  after: Kore
  effects: BackendEffect[]
}

export interface UncommittedObservation {
  kind: 'uncommitted'
  id: TransitionId
  ruleLabel?: string
  /** Effects attempted by a rolled-back transition; no leaf commits them. */
  effects: BackendEffect[]
  reason: 'rolled-back'
}

export type ObservationEvent =
  | TransitionObservation
  | EvaluationObservation
  | UncommittedObservation

export interface ObservationOptions {
  /** Exact executable rewrite, equation, simplification, or definedness ids. [] emits no events but retains every branch identity. Omit to include builtins. */
  rules?: string[]
}

export type SearchType = 'final' | 'all' | 'one-step' | 'one-or-more-steps'

export interface SearchOptions {
  state: Kore
  moduleName?: string
  searchType?: SearchType
  maxDepth?: number
  maxBreadth?: number
  /**
   * Maximum materialized states, witnesses, or matches. Truncation is always reported by a
   * `result-bound` entry. Path searches can enumerate exponentially many acyclic witnesses, so
   * callers should set this bound when the definition can converge repeatedly.
   */
  maxResults?: number
  maxSimplificationIterations?: number
  schemaVersion?: number
}

export interface SearchPatternOptions extends SearchOptions {
  pattern: Kore
}

export interface SearchState {
  state: Kore
  /** Diagnostics of the path in `trace`, each distinct one once, in first-occurrence order. */
  diagnostics?: BackendDiagnostic[]
  depth: number
  trace: BackendTraceEntry[]
  branch?: TransitionId[]
  observations?: ObservationEvent[]
}

export interface PathWitness {
  id: TransitionId[]
  state: Kore
  /** Diagnostics of this witness's path, as for `SearchState.diagnostics`. */
  diagnostics?: BackendDiagnostic[]
  depth: number
  trace: BackendTraceEntry[]
  observations?: ObservationEvent[]
}

export type BuiltinFailure =
  | { kind: 'wrong-arity'; hook: string; expected: number; actual: number }
  | { kind: 'unexpected-sort'; hook: string; expected: string; actual: string }
  | { kind: 'alternative-sorts-differ'; thenSort: string; elseSort: string }
  | { kind: 'incompatible-map-sorts'; left: string; right: string }
  | { kind: 'invalid-float-token'; hook: string; token: string }

export type TranslationFailure =
  | { kind: 'non-boolean-and'; term: Kore }
  | { kind: 'placeholder-out-of-bounds'; placeholder: number; arguments: number }
  | { kind: 'unsupported-predicate'; predicate: string }
  | { kind: 'parametric-sort'; sort: string }
  | { kind: 'smt-lemma-surplus-mappings'; rule: string; terms: Kore[] }
  | { kind: 'smt-lemma-surplus-predicates'; rule: string; predicates: Kore[] }
  | { kind: 'missing-smt-lemma-variable'; rule: string; variable: Kore }

export type ConditionIndeterminacy =
  | { kind: 'no-solver' }
  | { kind: 'implication-indeterminate' }
  | { kind: 'smt-unknown'; reason: string }
  | { kind: 'inconsistent-path-condition' }
  | { kind: 'untranslatable'; error: TranslationFailure }
  | { kind: 'non-functional-binding' }
  | { kind: 'unbound-result-variables'; variables: string[] }

/** A variable of an equation as an `undecided-condition` diagnostic's predicates spell it (`Eq-hVarY`) and as the definition names it (`VarY`). */
export type RuleVariable = { name: string; definitionName: string }

export type BackendDiagnostic =
  | {
      /** Reported only for an attempt whose outcome the simplification kept: the equation applied, or no other equation rewrote the subject and the simplification's result still holds it. An attempt whose `requires` was refuted, one that another equation superseded, one whose subject a later part of the same simplification dropped, and one made while simplifying the condition of an enclosing attempt that was itself refuted, superseded or dropped report nothing. */
      kind: 'undecided-condition'
      ruleId: string
      /** The first written sentence of the equation's axiom, the first of its ruleCatalog entry's `origins`; with `ruleId` it names an equation whose id is 'UNKNOWN'. */
      origin?: RuleOrigin
      reason: ConditionIndeterminacy
      /** The equation's instantiated `requires` (the equation was not used), or, once it held, the definedness of the terms the match bound (the result carries them). */
      predicates: Kore[]
      /** The equation's own variables that `predicates` name free, with their names in the definition. */
      ruleVariables: RuleVariable[]
    }
  | { kind: 'undecided-predicate'; predicate: Kore; reason: ConditionIndeterminacy }
  | { kind: 'simplification-budget-exhausted'; limit: number; subject: 'term' | 'predicates' }
  | {
      kind: 'rule-condition-unsimplified'
      ruleId: string
      /** The first written sentence of the rule's axiom, as for 'undecided-condition'; with `ruleId` it names a rule whose id is 'UNKNOWN'. */
      origin?: RuleOrigin
      limit: number
    }
  | {
      kind: 'rule-condition-failed'
      ruleId: string
      /** The first written sentence of the rule's axiom, as for 'undecided-condition'; with `ruleId` it names a rule whose id is 'UNKNOWN'. */
      origin?: RuleOrigin
      failure: SearchFailure
    }
  | { kind: 'unsupported-hook-unevaluated'; hook: string; reason: string }
  | { kind: 'undefined-initial-instances'; definedness: Kore[] }
  /**
   * The path read a value of `hook` the definition leaves open: in another model of the
   * definition this leaf may differ or be absent. A leaf without one is a leaf in every such
   * model; under `state-set` that covers its configuration and halt, not its depth and trace. A
   * path fact: it stays on the paths that depend on the work that found it, whatever became of
   * that work, and never causes or prevents a `state-set` merge.
   */
  | { kind: 'implementation-chosen-value'; hook: string; class: ChosenClass }
  /**
   * The path's decisions rest on an evaluation that found a claim of the definition contradicted
   * by its own equations (a condition it refuted, a candidate it removed, the halt); the fields
   * are those of `ContradictedClaim`. k-rust reads the undefined value as undefined, the answer
   * without the claim; in a model of the claim the decision may differ. A path fact: it stays on
   * the paths that depend on the work that found it, whatever became of that work, and never
   * causes or prevents a `state-set` merge.
   */
  | ({ kind: 'contradicted-claim' } & ContradictedClaim)

export type SmtFailure =
  | { kind: 'translation'; error: TranslationFailure }
  | { kind: 'unavailable' }
  | { kind: 'unknown'; reason: string }
  | { kind: 'inconsistent-ground-truth' }
  | { kind: 'malformed-script'; message: string }
  | { kind: 'missing-model' }
  | { kind: 'missing-model-value'; variable: Kore }
  | { kind: 'invalid-model-value'; variable: Kore; value: string }

export type SearchSatisfiability =
  | { kind: 'sat' }
  | { kind: 'unsat' }
  | { kind: 'unknown'; reason: string }
  | { kind: 'error'; error: SmtFailure }

export type SearchFailure =
  | { kind: 'stack-exhausted' }
  /** A macro or alias survived preprocessing; no solver query is reported. */
  | { kind: 'surviving-macro-or-alias'; symbol: string }
  | { kind: 'builtin'; error: BuiltinFailure }
  | { kind: 'conflicting-results'; rules: string[] }
  /** A rule query was undecided; error kind unavailable means this build lacks a solver. */
  | { kind: 'smt'; rule?: string; error: SmtFailure }
  /** A predicate query was undecided; error kind unavailable means this build lacks a solver. */
  | { kind: 'smt-predicate'; predicate: Kore; error: SmtFailure }
  | { kind: 'inconsistent-ground-truth'; rule?: string }
  | { kind: 'iteration-limit'; limit: number; term: Kore | null }
  | { kind: 'predicate-iteration-limit'; limit: number; predicate: Kore | null }
  | { kind: 'invalid-builtin-result-symbol'; hook: string; symbol: string }
  | { kind: 'unsupported-hook'; hook: string; reason: string; term: Kore }
  /** Unsupported unification remainder; an earlier unevaluated equation may still depend on a solver. */
  | { kind: 'match'; rule: string; bindings: BackendBinding[]; remainder: BackendTermPair[] }
  /** Rule variables remain unbound; this does not report a missing solver. */
  | { kind: 'instantiation'; rule: string; missingVariables: Kore[] }
  /** Rule condition needs a solver absent from this build. */
  | { kind: 'requires'; rule: string; predicates: Kore[] }
  | { kind: 'concreteness'; rule: string; variable: Kore }
  /** Priority-group remainder is undecided; satisfiability error kind unavailable means no solver. */
  | {
      kind: 'remainder'
      rules: string[]
      predicates: Kore[]
      satisfiability: SearchSatisfiability
    }

export type SearchIncomplete =
  | { kind: 'result-bound' }
  | { kind: 'depth-bound'; state: SearchState }
  | { kind: 'breadth-bound'; states: SearchState[] }
  | { kind: 'indeterminate'; state: SearchState; reason: SearchFailure }
  | { kind: 'cancelled'; state: SearchState }
  | { kind: 'simplification'; state: SearchState; error: SearchFailure }
  | {
      kind: 'match'
      state: SearchState
      bindings: BackendBinding[]
      remainder: BackendTermPair[]
    }
  | { kind: 'smt'; state: SearchState; error: SmtFailure }

export interface SearchResult {
  schemaVersion: number
  modality: 'state-set'
  states: SearchState[]
  effects: BackendEffect[]
  incomplete: SearchIncomplete[]
  /** Every initial state had no instance before any step; absent when false. */
  initialBottom?: true
  /**
   * Every distinct value the definition leaves open that the search read, in first-read order;
   * absent when none. When absent, every model of the definition that agrees with the request's
   * inputs and k-rust's stated readings gives the same results, entries and end.
   */
  implementationChosenValues?: ChosenValue[]
  /** Every distinct contradicted claim the search and its definition's load observed, as for `ExecutionResult.contradictedClaims`; absent when none. */
  contradictedClaims?: ContradictedClaim[]
  /** Every distinct `Bytes` result the memory allowance refused, as for `ExecutionResult.allowanceRefusals`; absent when none. */
  allowanceRefusals?: UnevaluatedHook[]
  /** Every other distinct application left unevaluated as an unsupported hook, as for `ExecutionResult.unsupportedHooks`; absent when none. */
  unsupportedHooks?: UnevaluatedHook[]
}

export interface PathSearchResult {
  schemaVersion: number
  modality: 'path-set'
  witnesses: PathWitness[]
  effects: BackendEffect[]
  incomplete: SearchIncomplete[]
  /** Every initial state had no instance before any step; absent when false. */
  initialBottom?: true
  /**
   * Every distinct value the definition leaves open that the search read, in first-read order;
   * absent when none. When absent, every model of the definition that agrees with the request's
   * inputs and k-rust's stated readings gives the same results, entries and end.
   */
  implementationChosenValues?: ChosenValue[]
  /** Every distinct contradicted claim the search and its definition's load observed, as for `ExecutionResult.contradictedClaims`; absent when none. */
  contradictedClaims?: ContradictedClaim[]
  /** Every distinct `Bytes` result the memory allowance refused, as for `ExecutionResult.allowanceRefusals`; absent when none. */
  allowanceRefusals?: UnevaluatedHook[]
  /** Every other distinct application left unevaluated as an unsupported hook, as for `ExecutionResult.unsupportedHooks`; absent when none. */
  unsupportedHooks?: UnevaluatedHook[]
}

export interface SearchMatch {
  bindings: BackendBinding[]
  constraints: Kore[]
  state: SearchState
  /** Diagnostics of matching `state` against the pattern, apart from `state.diagnostics`. */
  diagnostics?: BackendDiagnostic[]
}

export interface PatternSearchResult {
  schemaVersion: number
  modality: 'state-set'
  matches: SearchMatch[]
  effects: BackendEffect[]
  incomplete: SearchIncomplete[]
  /** Every initial state had no instance before any step; absent when false. */
  initialBottom?: true
  /**
   * Every distinct value the definition leaves open that the search read, in first-read order;
   * absent when none. When absent, every model of the definition that agrees with the request's
   * inputs and k-rust's stated readings gives the same results, entries and end.
   */
  implementationChosenValues?: ChosenValue[]
  /** Every distinct contradicted claim the search and its definition's load observed, as for `ExecutionResult.contradictedClaims`; absent when none. */
  contradictedClaims?: ContradictedClaim[]
  /** Every distinct `Bytes` result the memory allowance refused, as for `ExecutionResult.allowanceRefusals`; absent when none. */
  allowanceRefusals?: UnevaluatedHook[]
  /** Every other distinct application left unevaluated as an unsupported hook, as for `ExecutionResult.unsupportedHooks`; absent when none. */
  unsupportedHooks?: UnevaluatedHook[]
}

export interface PathSearchMatch {
  bindings: BackendBinding[]
  constraints: Kore[]
  witness: PathWitness
  /** Diagnostics of matching `witness` against the pattern, apart from `witness.diagnostics`. */
  diagnostics?: BackendDiagnostic[]
}

export interface PathPatternSearchResult {
  schemaVersion: number
  modality: 'path-set'
  matches: PathSearchMatch[]
  effects: BackendEffect[]
  incomplete: SearchIncomplete[]
  /** Every initial state had no instance before any step; absent when false. */
  initialBottom?: true
  /**
   * Every distinct value the definition leaves open that the search read, in first-read order;
   * absent when none. When absent, every model of the definition that agrees with the request's
   * inputs and k-rust's stated readings gives the same results, entries and end.
   */
  implementationChosenValues?: ChosenValue[]
  /** Every distinct contradicted claim the search and its definition's load observed, as for `ExecutionResult.contradictedClaims`; absent when none. */
  contradictedClaims?: ContradictedClaim[]
  /** Every distinct `Bytes` result the memory allowance refused, as for `ExecutionResult.allowanceRefusals`; absent when none. */
  allowanceRefusals?: UnevaluatedHook[]
  /** Every other distinct application left unevaluated as an unsupported hook, as for `ExecutionResult.unsupportedHooks`; absent when none. */
  unsupportedHooks?: UnevaluatedHook[]
}

export interface PatternOptions {
  state: Kore
  moduleName?: string
  schemaVersion?: number
}

export interface ImplicationOptions {
  antecedent: Kore
  consequent: Kore
  moduleName?: string
  schemaVersion?: number
}

export interface ImplicationCondition {
  predicate: Kore
  substitution: Kore
  witnesses: Kore
}

export interface ImplicationResult {
  schemaVersion: 2
  /**
   * `invalid` only when an instance of the antecedent outside the consequent was shown; a
   * refutation whose antecedent may be empty is `unknown`, with its condition and failure kept.
   */
  status: 'valid' | 'invalid' | 'unknown'
  condition?: ImplicationCondition
  /**
   * On an 'invalid' or 'unknown' result that found one, the part of the consequent that the
   * antecedent's instances outside it fail: 'term-mismatch' (the consequent's term does not
   * match; no condition), 'partial-coverage' (a remainder of that match fails; condition is the
   * part of the antecedent that would lie in the consequent), 'consequent-condition' (the term
   * matches and the consequent's condition is refuted, or on 'unknown' fails on part of the
   * antecedent; condition is the match's).
   */
  failure?:
    | 'term-mismatch'
    | 'partial-coverage'
    | 'consequent-condition'
}

export interface ModelResult {
  satisfiable: 'sat' | 'unsat' | 'unknown'
  substitution?: Kore
  reason?: string
}

export interface ProveOptions {
  moduleName?: string
  /** Claim label, unique id, or zero-based `#index`. Optional when there is exactly one claim. */
  claim?: string
  maxDepth?: number
  minDepth?: number
  breadthLimit?: number
  maxCounterexamples?: number
  maxSimplificationIterations?: number
  allowVacuous?: boolean
  depthFirst?: boolean
  stuckCheck?: boolean
  stepTimeoutMs?: number
  movingAverageTimeout?: boolean
  schemaVersion?: number
}

export interface ProofLeaf {
  state: Kore
  depth: number
  /**
   * 'proven': the state implies the claim's right-hand side. 'trusted': the claim is trusted and
   * this is its left-hand side, unexplored. 'stuck': outside the right-hand side with no
   * successor (it disproves the claim only under status 'disproved'). 'trivial': an undefined
   * step, a rule applies and its result is empty. 'vacuous': the constraint is bottom.
   * 'depth-bound', 'breadth-bound': left unexplored at the bound. 'timeout': the step passed its
   * deadline, ending the proof. 'stack-exhausted': the step ran out of stack, the proof goes on.
   * 'indeterminate': the implication, the step or a circularity was not decided.
   */
  outcome:
    | 'proven'
    | 'trusted'
    | 'stuck'
    | 'trivial'
    | 'vacuous'
    | 'depth-bound'
    | 'breadth-bound'
    | 'timeout'
    | 'stack-exhausted'
    | 'indeterminate'
  /** Why a 'timeout', 'stack-exhausted' or 'indeterminate' leaf ended there, for a reader only. */
  detail?: string
}

export interface ProofResult {
  claim: string
  status: 'proven' | 'disproved' | 'failed' | 'indeterminate' | 'depth-bound' | 'breadth-bound'
  exploredStates: number
  unexploredStates: number
  leaves: ProofLeaf[]
}

/**
 * A definition a fuzz campaign runs on: its sources, loaded and compiled for the Rust backend
 * as `krust kcompile` does, on krun's route.
 */
export interface FuzzDefinitionOptions {
  definition: string
  moduleName: string
  /** The module whose grammar parses the program; selected as `krust kcompile` does when absent. */
  syntaxModule?: string
  sourceName?: string
  /** Additional virtual files keyed by the names used in `requires`. */
  sources?: Readonly<Record<string, string>> | readonly Source[]
  markdownSelector?: string
  /** Load k-rust's embedded standard prelude. Defaults to true. */
  includePrelude?: boolean
}

export interface FuzzCampaignOptions extends FuzzDefinitionOptions {
  /** The mutant of a differential target: given exactly when the target is differential. */
  mutant?: FuzzDefinitionOptions
  campaign: FuzzCampaign
}

/**
 * A campaign specification, in the fuzz library's JSON (kebab-case fields).
 *
 * Exactly one of `program` and `kore-template` is given. `options`, `proposers` and `bounds`
 * are partial: each field given replaces the library default, and an unknown field throws.
 * The seed, the rejection cap and the budget's limit are canonical decimal strings, which
 * JavaScript reads and writes exactly at any size, as the report writes them.
 */
export interface FuzzCampaign {
  program?: FuzzProgramSource
  /** A KORE initial configuration whose free element variables are the holes, as KORE text. */
  'kore-template'?: string
  holes?: FuzzHole[]
  target: FuzzTarget
  options?: Partial<FuzzCaseOptions>
  proposers?: Partial<FuzzProposers>
  bounds?: Partial<FuzzGenerationBounds>
  /** Rejected cases after which the campaign ends with `rejected-out`; defaults to `"10000"`. */
  'rejection-cap'?: string
  seed: string
  /**
   * Recorded in the report as given. Without it, the report's `k-rust-revision` names this
   * package's build (`k-rust-napi <version>`, `+<revision>` when the build set
   * `K_RUST_REVISION`). Leave `thread-stack-size` out: the campaign runs on a thread of the
   * binding with a 256 MiB stack, as `krust fuzz` does, and the report records that size.
   */
  identity?: { 'k-rust-revision': string }
  budget: FuzzBudget
}

/** The unmodified program and its configuration-variable bindings (name without `$`, K text). */
export interface FuzzProgramSource {
  program?: { name: string; text: string; 'start-sort': string } | null
  'config-vars': [string, string][]
}

/** A hole value; integers are decimal strings and bytes lowercase hex. */
export type FuzzValue =
  | { int: string }
  | { bool: boolean }
  | { string: string }
  | { bytes: string }
  | { 'm-int': { width: number; value: string } }
  | { token: { sort: string; text: string } }
  | { list: FuzzValue[] }
  | { set: FuzzValue[] }
  | { map: [FuzzValue, FuzzValue][] }
  | { apply: { symbol: string; arguments: FuzzValue[] } }

export type FuzzHoleLocation =
  | { kind: 'span'; program: string; line?: number | null; find: string; literal: string }
  | { kind: 'config-var'; name: string }
  | { kind: 'kore-variable'; name: string }

export interface FuzzConstraints {
  range?: { min?: string; max?: string } | null
  length?: { min?: number | null; max?: number | null } | null
  elements?:
    | { collection: 'elements'; element: string }
    | { collection: 'entries'; key: string; value: string }
    | null
  choices?: FuzzValue[] | null
}

export interface FuzzHole {
  name: string
  sort: string
  location: FuzzHoleLocation
  constraints?: FuzzConstraints
  'allow-refused-sort'?: boolean
}

export type FuzzRuleRef =
  | { by: 'label'; value: string }
  | { by: 'unique-id'; value: string }
  | { by: 'source'; value: { source: string; line: number } }

/** Observer targets are library-only: one read from JSON carries no observer and throws. */
export type FuzzTargetKind =
  | { kind: 'rule'; rule: FuzzRuleRef; mode: 'fired' | 'covered' | 'condition-reached' }
  | { kind: 'pattern'; pattern: string; at: 'final' | 'any-state' }
  | { kind: 'differential' }
  | { kind: 'observer'; name: string }

export interface FuzzTarget {
  kind: FuzzTargetKind
  'run-to-completion': boolean
  'negated-property': boolean
}

export type FuzzPathMode = 'one-path' | 'all-paths'

export interface FuzzCaseOptions {
  paths: FuzzPathMode
  'max-depth': number | null
  'max-work': number | null
  'max-simplification-iterations': number
  'normal-end-pattern': string | null
  /**
   * Per-case wall-clock limit; a case it stops is `timeout`, outside the determinism contract.
   * `null`, the default, sets none.
   */
  'safety-limit-ms': number | null
  backend: { 'smt-timeout-ms': number; 'smt-retry-limit': number }
  shrink: boolean
}

export type FuzzProposerKind = 'blind' | 'dictionary' | 'climb' | 'corpus' | 'solve'

export interface FuzzProposers {
  'anchors-first': boolean
  explicit: Record<string, FuzzValue>[]
  /**
   * A weight of 0 disables a proposer; a positive weight for a proposer this build does not provide
   * throws.
   */
  weights: Partial<Record<FuzzProposerKind, number>>
}

export interface FuzzGenerationBounds {
  'int-bits': number
  length: number
  depth: number
}

export type FuzzBudget = { cases: string } | { work: string }

export type FuzzOutcomeClass =
  | 'hit'
  | 'miss'
  | 'stuck'
  | 'reached-unfinished'
  | 'depth-bound'
  | 'work-bound'
  | 'timeout'
  | 'undefined'
  | 'unsupported'
  | 'rejected'
  | 'baseline-incomplete'

export type FuzzDefinitionRole = 'baseline' | 'mutant'

export interface FuzzDefinitionIdentity {
  role: FuzzDefinitionRole
  'main-module': string
  'syntax-module': string
  'execution-digest': string
  route: 'source-execution' | 'from-definition'
  'frontend-digest': string
  'execution-definition-digest': string
  'syntax-definition-digest': string
  'initial-configuration-digest': string | null
  'execution-rewrite-order-digest': string | null
}

export interface FuzzReportIdentity {
  'engine-version': number
  'k-rust-revision': string
  definitions: FuzzDefinitionIdentity[]
  'program-digest': string
  'overlay-digest': string
  'target-digest': string
  options: FuzzCaseOptions
  proposers: FuzzProposers
  bounds: FuzzGenerationBounds
  caps: {
    'int-bits': number
    length: number
    depth: number
    enumeration: number
    'value-size': number
  }
  'rejection-cap': string
  seed: string
  budget: FuzzBudget
  'thread-stack-size': string | null
  solver: 'z3' | 'none'
}

export interface FuzzHoleValue {
  name: string
  location: FuzzHoleLocation
  'k-text'?: string
  kore: string
  value: FuzzValue
}

export interface FuzzWitnessCase {
  holes: FuzzHoleValue[]
  class: FuzzOutcomeClass
  sides: {
    role: FuzzDefinitionRole
    'initial-configuration': string
    'final-configurations': string[]
  }[]
  reaching: { role: FuzzDefinitionRole; leaf?: number }
  kill?: 'added-end' | 'removed-end'
  steps?: number
}

export interface FuzzWitness {
  label: 'hit' | 'property-failure'
  first: FuzzWitnessCase
  shrunk: FuzzWitnessCase | null
  'clean-leaf-facts': string[]
  'krun-command': string | null
}

/** The bounded statement of a campaign without a witness; never a claim that none exists. */
export interface FuzzNoWitness {
  statement: string
  'path-mode': FuzzPathMode
}

export type FuzzCampaignOutcome =
  | { status: 'witness-found'; witness: FuzzWitness }
  | { status: 'no-witness-found'; 'no-witness': FuzzNoWitness }
  | { status: 'equivalent' }
  | { status: 'rejected-out'; 'no-witness': FuzzNoWitness }
  | { status: 'cancelled'; 'no-witness': FuzzNoWitness }
  | { status: 'aborted'; reason: string; 'no-witness': FuzzNoWitness }

export type FuzzRejectionReason =
  | 'generation'
  | 'constraint'
  | 'print'
  | 'assembly'
  | 'round-trip'
  | 'backend-refused'

export interface FuzzTotals {
  cases: number
  work: number
  classes: Partial<Record<FuzzOutcomeClass, number>>
  'rejection-rate-permille': number
  rejections: Partial<Record<FuzzRejectionReason, number>>
  coverage: { applied: string[]; matched: string[] }
  'target-blocked': number
  'best-score': number[] | null
  'outside-determinism': number
  unconfirmed: number
  'case-sequence-digest': string
}

/** A campaign's report: schema `krust-fuzz-report`, version 1 (docs/compatibility.md). */
export interface FuzzReport {
  schema: 'krust-fuzz-report'
  version: number
  identity: FuzzReportIdentity
  outcome: FuzzCampaignOutcome
  totals: FuzzTotals
  'load-records': { kind: string; detail: string }[]
  'sort-overrides': { hole: string; sort: string; refusal: string }[]
  warnings: string[]
  'engine-defects': { case: number | null; description: string }[]
}

export interface FuzzCampaignResult {
  /** The report's canonical JSON: equal reports are equal strings. */
  json: string
  report: FuzzReport
}

/** A persistent native backend with cached parsed modules and Z3 preludes. */
export class Backend {
  readonly #native: NativeBackend

  constructor(native: NativeBackend) {
    this.#native = native
  }

  get capabilities(): BackendCapabilities {
    return JSON.parse(this.#native.capabilities) as BackendCapabilities
  }

  ruleCatalog(moduleName?: string): CompiledRule[] {
    return JSON.parse(this.#native.ruleCatalog(moduleName)) as CompiledRule[]
  }

  execute(options: ExecuteOptions): ExecutionResult {
    return JSON.parse(this.#native.execute(JSON.stringify(options))) as ExecutionResult
  }

  executeObserved(
    options: ExecuteOptions,
    observation: ObservationOptions = {},
  ): ExecutionResult {
    return JSON.parse(
      this.#native.executeObserved(JSON.stringify({ request: options, rules: observation.rules })),
    ) as ExecutionResult
  }

  search(options: SearchOptions): SearchResult {
    return JSON.parse(this.#native.search(JSON.stringify(options))) as SearchResult
  }

  searchPaths(options: SearchOptions): PathSearchResult {
    return JSON.parse(this.#native.searchPaths(JSON.stringify(options))) as PathSearchResult
  }

  searchPattern(options: SearchPatternOptions): PatternSearchResult {
    return JSON.parse(this.#native.searchPattern(JSON.stringify(options))) as PatternSearchResult
  }

  searchPatternPaths(options: SearchPatternOptions): PathPatternSearchResult {
    return JSON.parse(
      this.#native.searchPatternPaths(JSON.stringify(options)),
    ) as PathPatternSearchResult
  }

  searchObserved(
    options: SearchOptions,
    observation: ObservationOptions = {},
  ): SearchResult {
    return JSON.parse(
      this.#native.searchObserved(JSON.stringify({ request: options, rules: observation.rules })),
    ) as SearchResult
  }

  searchPathsObserved(
    options: SearchOptions,
    observation: ObservationOptions = {},
  ): PathSearchResult {
    return JSON.parse(
      this.#native.searchPathsObserved(
        JSON.stringify({ request: options, rules: observation.rules }),
      ),
    ) as PathSearchResult
  }

  searchPatternObserved(
    options: SearchPatternOptions,
    observation: ObservationOptions = {},
  ): PatternSearchResult {
    return JSON.parse(
      this.#native.searchPatternObserved(
        JSON.stringify({ request: options, rules: observation.rules }),
      ),
    ) as PatternSearchResult
  }

  searchPatternPathsObserved(
    options: SearchPatternOptions,
    observation: ObservationOptions = {},
  ): PathPatternSearchResult {
    return JSON.parse(
      this.#native.searchPatternPathsObserved(
        JSON.stringify({ request: options, rules: observation.rules }),
      ),
    ) as PathPatternSearchResult
  }

  simplify(options: PatternOptions): Kore {
    return JSON.parse(this.#native.simplify(JSON.stringify(options))) as Kore
  }

  implies(options: ImplicationOptions): ImplicationResult {
    return JSON.parse(this.#native.implies(JSON.stringify(options))) as ImplicationResult
  }

  getModel(options: PatternOptions): ModelResult {
    return JSON.parse(this.#native.getModel(JSON.stringify(options))) as ModelResult
  }

  prove(options: ProveOptions = {}): ProofResult {
    return JSON.parse(this.#native.prove(JSON.stringify(options))) as ProofResult
  }

  addModule(module: string, options: { nameAsId?: boolean } = {}): string {
    return this.#native.addModule(module, options.nameAsId)
  }
}

/** Create a persistent native backend from compiled textual KORE. */
export function createBackend(options: CreateBackendOptions): Backend {
  return new Backend(createBackendNative(options))
}

/** Compile an in-memory K definition and immediately create a persistent native backend. */
export function compileBackend(options: CompileDefinitionOptions): Backend {
  const nativeOptions: NativeCompileDefinitionOptions = {
    ...options,
    sources: normalizeSources(options.sources),
  }
  return new Backend(compileBackendNative(nativeOptions))
}

/** Parse a concrete K program with an in-memory definition and virtual source graph. */
export function parseProgram(options: ParseProgramOptions): ParsedProgram {
  const nativeOptions: NativeParseProgramOptions = {
    ...options,
    sources: normalizeSources(options.sources),
  }
  const parsed = parseProgramNative(nativeOptions)
  return {
    text: parsed.text,
    kast: JSON.parse(parsed.json) as Kast,
    diagnostics: parsed.diagnostics as Diagnostic[],
  }
}

/** Compile an in-memory K definition into backend-facing textual KORE artifacts. */
export function compileDefinition(options: CompileDefinitionOptions): CompiledDefinition {
  const nativeOptions: NativeCompileDefinitionOptions = {
    ...options,
    sources: normalizeSources(options.sources),
  }
  const compiled = compileDefinitionNative(nativeOptions)
  return {
    ...compiled,
    diagnostics: compiled.diagnostics as Diagnostic[],
  }
}

/** Parse textual KAST and return both canonical text and typed KAST JSON v4. */
export function parseKast(source: string): SerializedKast {
  const parsed = parseKastNative(source)
  return { text: parsed.text, kast: JSON.parse(parsed.json) as Kast }
}

/**
 * Print typed KAST JSON v4 using k-rust's canonical textual printer.
 *
 * The text reads back through `parseKast` as the same term, up to sequence flattening and the
 * identification of a one-item sequence with its item.
 * Throws for a term textual KAST cannot spell: a variable with a sort, a variable name outside
 * `[_A-Z][A-Za-z0-9'_]*` (such as a set variable's `@X`), or an application of the empty label.
 */
export function printKast(kast: Kast): string {
  return printKastNative(JSON.stringify(kast))
}

/** Parse textual KORE and return both canonical text and typed KORE JSON v1. */
export function parseKore(source: string, width?: number): SerializedKore {
  const parsed = parseKoreNative(source, width)
  return { text: parsed.text, kore: JSON.parse(parsed.json) as Kore }
}

/** Print typed KORE JSON v1 using k-rust's width-aware printer. */
export function printKore(kore: Kore, width?: number): string {
  return printKoreNative(JSON.stringify(kore), width)
}

/** Parse and consistently pretty-print a complete textual KORE definition. */
export function formatKoreDefinition(source: string, width?: number): string {
  return formatKoreDefinitionNative(source, width)
}

/**
 * Run one `krust fuzz` campaign to its end: compile the definition (and a differential target's
 * mutant), craft hole values until the budget is spent or a witness is confirmed, and return the
 * report. The call is synchronous and holds the calling thread for the whole campaign; bound it
 * with `campaign.budget` and the case options, and call it from a worker thread in
 * latency-sensitive applications. A campaign that runs returns its report whatever its outcome;
 * a malformed specification, a definition that does not compile, and a campaign the library
 * refuses throw.
 */
export function runFuzzCampaign(options: FuzzCampaignOptions): FuzzCampaignResult {
  const { mutant, campaign, ...baseline } = options
  const json = runFuzzCampaignNative({
    ...nativeFuzzDefinition(baseline),
    mutant: mutant === undefined ? undefined : nativeFuzzDefinition(mutant),
    campaign: JSON.stringify(campaign),
  })
  return { json, report: JSON.parse(json) as FuzzReport }
}

function nativeFuzzDefinition(options: FuzzDefinitionOptions): NativeFuzzDefinition {
  return { ...options, sources: normalizeSources(options.sources) }
}

function normalizeSources(
  sources: ParseProgramOptions['sources'],
): NativeParseProgramOptions['sources'] {
  if (sources === undefined || Array.isArray(sources)) return sources
  return Object.entries(sources).map(([name, text]) => ({ name, text }))
}
