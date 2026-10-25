const assert = require('node:assert/strict')
const fs = require('node:fs')
const path = require('node:path')
const test = require('node:test')

const {
  compileBackend,
  compileDefinition,
  createBackend,
  parseKast,
  parseKore,
  parseProgram,
  printKast,
  printKore,
  runFuzzCampaign,
} = require('../dist/index.js')

const backendDefinition = String.raw`[]
module MAIN
  sort SortS{} []
  alias weakExistsFinally{A}(A) : A where weakExistsFinally{A}(@X:A) := @X:A []
  symbol a{}() : SortS{} [constructor{}()]
  symbol b{}() : SortS{} [constructor{}()]
  symbol c{}() : SortS{} [constructor{}()]
  symbol wrap{}(SortS{}) : SortS{} [constructor{}()]
  axiom{} \rewrites{SortS{}}(
    \and{SortS{}}(a{}(), \top{SortS{}}()),
    \and{SortS{}}(b{}(), \top{SortS{}}())
  ) [label{}("a-to-b")]
  axiom{} \rewrites{SortS{}}(
    \and{SortS{}}(b{}(), \top{SortS{}}()),
    \and{SortS{}}(c{}(), \top{SortS{}}())
  ) [label{}("b-to-c")]
  claim{} \implies{SortS{}}(
    \and{SortS{}}(\top{SortS{}}(), a{}()),
    weakExistsFinally{SortS{}}(\and{SortS{}}(c{}(), \top{SortS{}}()))
  ) [label{}("reaches-c")]
endmodule []`

test('publishes an indeterminate execution cause through the native binding', () => {
  const definitionKore = String.raw`[]
module MAIN
  sort SortS{} []
  symbol wrap{}(SortS{}) : SortS{} [constructor{}()]
  symbol pair{}(SortS{}, SortS{}) : SortS{}
    [function{}(), total{}(), injective{}(), no-evaluators{}()]
  axiom{} \rewrites{SortS{}}(
    \and{SortS{}}(wrap{}(I:SortS{}), \top{SortS{}}()),
    pair{}(I:SortS{}, I:SortS{})
  ) [label{}("duplicate")]
endmodule []`
  const backend = createBackend({ definitionKore, moduleName: 'MAIN' })
  const leaf = backend.execute({ state: parseKore('wrap{}(@Y:SortS{})').kore }).leaves[0]
  assert.equal(leaf.reason, 'indeterminate')
  assert.equal(leaf.cause.kind, 'match')
  assert.equal(leaf.cause.rule, 'duplicate')
})

test('exposes a simplification budget diagnostic on its execution leaf', () => {
  const definitionKore = fs.readFileSync(
    path.join(__dirname, '../../k-rust/tests/fixtures/execution-budget.kore'),
    'utf8',
  )
  const backend = createBackend({ definitionKore, moduleName: 'MAIN' })
  const leaf = backend.execute({ state: parseKore('start{}()').kore, maxSimplificationIterations: 3 }).leaves[0]
  assert.deepEqual(leaf.diagnostics, [
    { kind: 'simplification-budget-exhausted', limit: 3, subject: 'term' },
  ])
})

test('exposes the diagnostic on only the branch candidate that emitted it', () => {
  const definitionKore = fs.readFileSync(
    path.join(__dirname, '../../k-rust/tests/fixtures/execution-candidates.kore'),
    'utf8',
  )
  const backend = createBackend({ definitionKore, moduleName: 'MAIN' })
  const leaf = backend.execute({
    state: parseKore('start{}()').kore,
    maxSimplificationIterations: 3,
    stopAtBranch: true,
  }).leaves[0]
  assert.equal(leaf.reason, 'branch')
  assert.equal(leaf.diagnostics, undefined)
  assert.deepEqual(
    leaf.candidates.find(({ label }) => label === 'to-g').diagnostics,
    [{ kind: 'simplification-budget-exhausted', limit: 3, subject: 'term' }],
  )
  assert.equal(leaf.candidates.find(({ label }) => label === 'to-b').diagnostics, undefined)
})

const termExhausted = [{ kind: 'simplification-budget-exhausted', limit: 3, subject: 'term' }]
// The fixture's KORE carries no source or location attributes, so a rule's origin is only its
// sentence: its index among all of MAIN's sentences (the sort, nine symbols, then the axioms).
const sentenceIndex = { 'norm-c': 11, 'check-ok': 12 }
const conditionExhausted = (ruleId) => [
  { kind: 'simplification-budget-exhausted', limit: 3, subject: 'predicates' },
  {
    kind: 'rule-condition-unsimplified',
    ruleId,
    origin: { source: null, location: null, sentence: { module: 'MAIN', index: sentenceIndex[ruleId] } },
    limit: 3,
  },
]
const ending = (entries, field, symbol) =>
  entries.find((entry) => JSON.stringify(entry[field]).includes(`"name":"${symbol}"`))

test('exposes each search state, witness and match its own diagnostics', () => {
  const definitionKore = fs.readFileSync(
    path.join(__dirname, '../../k-rust/tests/fixtures/search-diagnostics.kore'),
    'utf8',
  )
  const backend = createBackend({ definitionKore, moduleName: 'MAIN' })
  const search = { state: parseKore('start{}()').kore, maxSimplificationIterations: 3 }
  const states = backend.search(search).states.map((state) => ({ state }))
  assert.deepEqual(ending(states, 'state', 'g').state.diagnostics, termExhausted)
  assert.equal(ending(states, 'state', 'b').state.diagnostics, undefined)
  assert.deepEqual(ending(states, 'state', 'c').state.diagnostics, conditionExhausted('norm-c'))
  const witnesses = backend.searchPaths(search).witnesses.map((witness) => ({ witness }))
  assert.deepEqual(ending(witnesses, 'witness', 'g').witness.diagnostics, termExhausted)
  assert.equal(ending(witnesses, 'witness', 'b').witness.diagnostics, undefined)

  const pattern = parseKore(
    '\\and{SortS{}}(X:SortS{}, \\equals{SortS{}, SortS{}}(check{}(X:SortS{}), ok{}()))',
  ).kore
  const matches = backend.searchPattern({ ...search, pattern }).matches
  assert.equal(ending(matches, 'state', 'b').state.diagnostics, undefined)
  assert.deepEqual(ending(matches, 'state', 'b').diagnostics, conditionExhausted('check-ok'))
  assert.deepEqual(ending(matches, 'state', 'c').state.diagnostics, conditionExhausted('norm-c'))
  assert.deepEqual(ending(matches, 'state', 'c').diagnostics, conditionExhausted('check-ok'))
  const pathMatches = backend.searchPatternPaths({ ...search, pattern }).matches
  assert.equal(ending(pathMatches, 'witness', 'b').witness.diagnostics, undefined)
  assert.deepEqual(ending(pathMatches, 'witness', 'b').diagnostics, conditionExhausted('check-ok'))
})

const koreSortS = { tag: 'SortApp', name: 'SortS', args: [] }

function deeplyNestedKore(depth) {
  let term = { tag: 'Top', sort: koreSortS }
  for (let index = 0; index < depth; index += 1) {
    term = { tag: 'Not', sort: koreSortS, arg: term }
  }
  return { format: 'KORE', version: 1, term }
}

function deeplyNestedBackendState(depth) {
  let term = { tag: 'App', name: 'a', sorts: [], args: [] }
  for (let index = 0; index < depth; index += 1) {
    term = { tag: 'App', name: 'wrap', sorts: [], args: [term] }
  }
  return { format: 'KORE', version: 1, term }
}

test('exposes the compiled rule catalog', () => {
  const backend = createBackend({ definitionKore: backendDefinition, moduleName: 'MAIN' })
  const catalog = backend.ruleCatalog()
  assert.deepEqual(backend.ruleCatalog('MAIN'), catalog)
  assert.deepEqual(
    catalog.filter((rule) => rule.kind === 'rewrite').map((rule) => rule.label),
    ['a-to-b', 'b-to-c'],
  )
  assert.ok(catalog.every((rule) => typeof rule.id === 'string'))
  assert.ok(catalog.every((rule) => Array.isArray(rule.origins)))
  assert.ok(catalog.every((rule) => typeof rule.sharedIdentity === 'boolean'))
})

test('parses programs through virtual requires', () => {
  const parsed = parseProgram({
    definition: `
      requires "../base.k"
      module MAIN
        imports BASE
        syntax Exp ::= Int
      endmodule
    `,
    moduleName: 'MAIN',
    sort: 'Exp',
    program: '42',
    sourceName: 'definitions/nested/main.k',
    sources: {
      'definitions/base.k': `
        module BASE
          syntax Int ::= r"[0-9]+" [token]
        endmodule
      `,
    },
    includePrelude: false,
  })

  assert.equal(parsed.text, '#token("42","Int")')
  assert.equal(parsed.kast.term.node, 'KToken')
  assert.equal(parsed.kast.term.token, '42')
})

test('presents Z3-inferred parametric labels like reference kast', () => {
  const parsed = parseProgram({
    definition: `
      module MAIN
        syntax Int ::= r"[0-9]+" [token]
        syntax Box ::= "box(" Int ")" [symbol(box)]
        syntax {S} S ::= "same(" S ")" [symbol(same)]
      endmodule
    `,
    moduleName: 'MAIN',
    sort: 'Box',
    program: 'box(same(1))',
    includePrelude: false,
  })

  assert.equal(parsed.text, 'box(same(#token("1","Int")))')
  assert.deepEqual(parsed.kast.term.args[0].label.params, [])
})

test('compiles definitions through the full native pipeline', () => {
  const compiled = compileDefinition({
    definition: `
      module MAIN
        syntax Num ::= "one" [symbol(one)]
        syntax Box ::= "box(" Num ")" [function, symbol(box)]
        syntax {S} S ::= "same(" S ")" [symbol(same)]
        rule box(same(one)) => box(one)
      endmodule
    `,
    moduleName: 'MAIN',
    includePrelude: false,
  })

  assert.match(compiled.definitionKore, /module MAIN/)
  assert.match(compiled.definitionKore, /Lblsame/)
  assert.match(compiled.syntaxDefinitionKore, /module MAIN/)
  assert.equal(compiled.macrosKore, '\n')
})

test('rejects a value-building parametric application at a token sort', () => {
  assert.throws(
    () =>
      compileDefinition({
        definition: `
          module MAIN
            syntax Int ::= r"[0-9]+" [token]
            syntax Box ::= "box(" Int ")" [function, symbol(box)]
            syntax {S} S ::= "same(" S ")" [symbol(same)]
            rule box(same(1)) => box(1)
          endmodule
        `,
        moduleName: 'MAIN',
        includePrelude: false,
      }),
    /the instance of `same`.*is at sort Int/,
  )
})

test('round-trips KAST and KORE through typed JSON', () => {
  const kast = parseKast('#token("x","Id")')
  assert.equal(printKast(kast.kast), kast.text)

  const kore = parseKore('X:S')
  assert.equal(printKore(kore.kore), kore.text)
})

test('prints KAST text that reads back as the printed term', () => {
  for (const [source, text] of [
    ['``X~>foo(.KList)``=>Y', '``X~>foo(.KList)``=>Y'],
    ['X~>``foo(.KList)=>Y``', 'X~>``foo(.KList)=>Y``'],
    ['``X=>Y``=>Z', '``X=>Y``=>Z'],
    ['``X #as Y``=>Z', '``X #as Y``=>Z'],
  ]) {
    const parsed = parseKast(source)
    assert.equal(parsed.text, text)
    assert.equal(printKast(parsed.kast), text)
    assert.deepEqual(parseKast(printKast(parsed.kast)).kast, parsed.kast)
  }
  const rewrite = parseKast('``X~>foo(.KList)``=>Y').kast
  assert.equal(rewrite.term.node, 'KRewrite')
  assert.equal(rewrite.term.lhs.node, 'KSequence')

  const variable = parseKast('X').kast
  const sort = parseKast('#token("1","Int")').kast.term.sort
  assert.throws(
    () => printKast({ ...variable, term: { ...variable.term, sort } }),
    /variable X has sort Int/,
  )
  assert.throws(
    () => printKast({ ...variable, term: { ...variable.term, name: '@X' } }),
    /not readable as textual KAST/,
  )
})

test('reads deep typed JSON without a surface-specific recursion limit', () => {
  const kore = deeplyNestedKore(160)
  assert.equal((printKore(kore).match(/\\not/g) ?? []).length, 160)

  const kast = JSON.parse(
    fs.readFileSync(
      path.join(
        __dirname,
        '../../k-rust/tests/fixtures/reference/kast/json/deep-70/ref-p2.json',
      ),
      'utf8',
    ),
  )
  assert.equal(
    (printKast(kast).match(/g\(_\)_TEST-SYNTAX_Exp_Exp/g) ?? []).length,
    70,
  )

  const backend = createBackend({ definitionKore: backendDefinition, moduleName: 'MAIN' })
  const execution = backend.execute({
    state: deeplyNestedBackendState(200),
    maxDepth: 0,
  })
  assert.equal(execution.leaves.length, 1)
})

test('runs the complete persistent native backend API', () => {
  const backend = createBackend({ definitionKore: backendDefinition, moduleName: 'MAIN' })
  const a = parseKore('a{}()').kore
  const c = parseKore('c{}()').kore

  assert.equal(backend.capabilities.smt, true)
  const execution = backend.execute({ state: a, maxDepth: 2 })
  assert.equal(printKore(execution.leaves[0].state), 'c{}()')
  assert.equal(printKore(backend.simplify({ state: a })), 'a{}()')
  const implication = backend.implies({ antecedent: c, consequent: c })
  assert.equal(implication.schemaVersion, 2)
  assert.equal(implication.status, 'valid')
  assert.equal(printKore(implication.condition.predicate), '\\top{SortS{}}()')
  assert.equal(printKore(implication.condition.substitution), '\\top{SortS{}}()')
  assert.equal(printKore(implication.condition.witnesses), '\\top{SortS{}}()')
  assert.equal(backend.getModel({ state: parseKore('\\top{SortS{}}()').kore }).satisfiable, 'unknown')
  assert.equal(backend.prove({ claim: 'reaches-c' }).status, 'proven')

  const added = String.raw`module EXTRA
    import MAIN []
    axiom{} \rewrites{SortS{}}(
      \and{SortS{}}(c{}(), \top{SortS{}}()),
      \and{SortS{}}(a{}(), \top{SortS{}}())
    ) [label{}("c-to-a")]
  endmodule []`
  backend.addModule(added, { nameAsId: true })
  const addedExecution = backend.execute({ state: c, moduleName: 'EXTRA', maxDepth: 1 })
  assert.equal(printKore(addedExecution.leaves[0].state), 'a{}()')
})

test('searches and observes the persistent native backend graph', () => {
  const backend = createBackend({ definitionKore: backendDefinition, moduleName: 'MAIN' })
  const a = parseKore('a{}()').kore
  const c = parseKore('c{}()').kore

  assert.equal(backend.capabilities.search, true)
  assert.equal(backend.capabilities.observation, true)

  const states = backend.search({ state: a, searchType: 'final' })
  assert.equal(states.schemaVersion, 1)
  assert.equal(states.modality, 'state-set')
  assert.equal(states.states.length, 1)
  assert.equal(printKore(states.states[0].state), 'c{}()')

  const paths = backend.searchPaths({ state: a, searchType: 'final' })
  assert.equal(paths.modality, 'path-set')
  assert.deepEqual(
    paths.witnesses[0].id.map(({ rule }) => rule),
    ['a-to-b', 'b-to-c'],
  )

  const pattern = backend.searchPattern({ state: a, pattern: c })
  assert.equal(pattern.matches.length, 1)
  assert.equal(pattern.modality, 'state-set')
  const patternPaths = backend.searchPatternPaths({ state: a, pattern: c })
  assert.equal(patternPaths.matches.length, 1)
  assert.equal(patternPaths.modality, 'path-set')

  const observed = backend.searchObserved(
    { state: a },
    { rules: ['a-to-b'] },
  )
  assert.equal(observed.states[0].branch.length, 2)
  assert.deepEqual(
    observed.states[0].observations.map(({ id }) => id.rule),
    ['a-to-b'],
  )
  assert.equal(backend.executeObserved({ state: a }).leaves[0].observations.length, 2)
  assert.equal(backend.execute({ state: a }).modality, 'state-set')
  assert.equal(
    backend.executeObserved({ state: a, resultModality: 'path-set' }).modality,
    'path-set',
  )
  assert.equal(backend.capabilities.coverage, true)
  assert.equal(backend.capabilities.coverageOffered, true)
  assert.equal(backend.capabilities.coverageCounts, true)
  assert.equal(backend.capabilities.coverageConditions, true)
  assert.equal(backend.capabilities.coverageCommitted, true)
  assert.equal(backend.capabilities.stateMatches, true)
  assert.equal(backend.capabilities.stackStops, true)
  assert.equal(backend.capabilities.smtUnknowns, true)
  assert.equal(backend.capabilities.implementationChosenValues, true)
  assert.equal(backend.execute({ state: a }).implementationChosenValues, undefined)
  assert.equal(backend.search({ state: a }).implementationChosenValues, undefined)
  assert.equal(backend.capabilities.contradictedClaims, true)
  assert.equal(backend.capabilities.allowanceRefusals, true)
  assert.equal(backend.capabilities.unsupportedHooks, true)
  assert.equal(backend.execute({ state: a }).contradictedClaims, undefined)
  assert.equal(backend.execute({ state: a }).allowanceRefusals, undefined)
  assert.equal(backend.search({ state: a }).contradictedClaims, undefined)
  assert.equal(backend.search({ state: a }).allowanceRefusals, undefined)
  assert.equal(backend.search({ state: a }).unsupportedHooks, undefined)
  assert.equal(backend.execute({ state: a }).unsupportedHooks, undefined)
  assert.equal(backend.execute({ state: a }).smtUnknowns, undefined)
  assert.equal(backend.execute({ state: a }).coverage, undefined)
  assert.deepEqual(backend.execute({ state: a, collectCoverage: true }).coverage, {
    applied: ['a-to-b', 'b-to-c'],
    matched: ['a-to-b', 'b-to-c'],
  })
  assert.deepEqual(
    backend.execute({ state: a, collectCoverage: true, collectOffered: true }).coverage,
    {
      applied: ['a-to-b', 'b-to-c'],
      matched: ['a-to-b', 'b-to-c'],
      offered: ['a-to-b', 'b-to-c'],
    },
  )
  assert.throws(
    () => backend.execute({ state: a, collectOffered: true }),
    /collectOffered requires collectCoverage/,
  )
  assert.deepEqual(
    backend.execute({ state: a, collectCoverage: true, collectCounts: true }).coverage,
    {
      applied: ['a-to-b', 'b-to-c'],
      matched: ['a-to-b', 'b-to-c'],
      appliedCounts: { 'a-to-b': 1, 'b-to-c': 1 },
    },
  )
  assert.throws(
    () => backend.execute({ state: a, collectCounts: true }),
    /collectCounts requires collectCoverage/,
  )
  assert.throws(
    () => backend.execute({ state: a, collectConditions: { rules: ['a-to-b'] } }),
    /collectConditions requires collectCoverage/,
  )
  assert.deepEqual(
    backend.execute({ state: a, collectCoverage: true, collectCommitted: true }).coverage,
    {
      applied: ['a-to-b', 'b-to-c'],
      matched: ['a-to-b', 'b-to-c'],
      committed: ['a-to-b', 'b-to-c'],
    },
  )
  assert.throws(
    () => backend.execute({ state: a, collectCommitted: true }),
    /collectCommitted requires collectCoverage/,
  )
  assert.equal(backend.execute({ state: a }).stateMatches, undefined)
  const matched = backend.execute({ state: a, matchStates: { pattern: c } }).stateMatches
  assert.equal(matched.firstCleanReach.depth, 2)
  assert.equal(matched.matched, 3)
  assert.equal(matched.refuted, 2)
  assert.ok(backend.execute({ state: a }).leaves.every(({ trace }) => trace.length > 0))
  assert.ok(backend.execute({ state: a, trace: false }).leaves.every(({ trace }) => trace.length === 0))

  assert.throws(() => backend.search({ state: a, schemaVersion: 99 }), /schema version 99/)
  assert.throws(() => backend.search({ state: a, maxDeph: 1 }), /unknown field.*maxDeph/i)
})

test('compileBackend compiles and creates a native session', () => {
  const backend = compileBackend({
    definition: `module MAIN
      syntax State ::= "a" [function, symbol(a)] | "b" [symbol(b)]
      rule a => b
    endmodule`,
    moduleName: 'MAIN',
    includePrelude: false,
  })
  assert.equal(backend.capabilities.execution, true)
  assert.equal(backend.capabilities.smt, true)
  assert.equal(printKore(backend.simplify({ state: parseKore('Lbla{}()').kore })), 'Lblb{}()')
})

const readFixture = name =>
  fs.readFileSync(path.join(__dirname, '../../k-rust-fuzz/tests/data/imp', name), 'utf8')
const SOLVER = 'z3'

// The IMP campaign of the crate's own test (src/fuzz.rs): blind values for `x` and `y` of `le.imp`
// until one falsifies the claim that `r` ends as 1, which any `x > y` does.
const impCampaign = (campaign = {}) => ({
  definition: readFixture('imp.k'),
  moduleName: 'IMP',
  sourceName: 'imp.k',
  includePrelude: true,
  campaign: {
    program: {
      program: { name: 'le.imp', text: readFixture('le.imp'), 'start-sort': 'Pgm' },
      'config-vars': [],
    },
    holes: [
      { name: 'X', sort: 'Int', location: { kind: 'span', program: 'le.imp', find: 'x = 3;', literal: '3' } },
      { name: 'Y', sort: 'Int', location: { kind: 'span', program: 'le.imp', find: 'y = 5;', literal: '5' } },
    ],
    target: {
      kind: {
        kind: 'pattern',
        pattern: '<k> .K </k> <state> (#token("r", "Id") |-> R:Int) _:Map </state> requires R =/=Int 1',
        at: 'final',
      },
      'run-to-completion': false,
      'negated-property': true,
    },
    seed: '24301',
    identity: { 'k-rust-revision': 'binding-test' },
    budget: { cases: '64' },
    ...campaign,
  },
})

test('runs one fuzz campaign on IMP to a confirmed witness', () => {
  const { json, report } = runFuzzCampaign(impCampaign())
  assert.equal(report.schema, 'krust-fuzz-report')
  assert.equal(report.version, 9)
  assert.equal(report.identity.solver, SOLVER)
  assert.equal(report.identity.seed, '24301')
  assert.deepEqual(report.identity.budget, { cases: '64' })
  assert.equal(report.outcome.status, 'witness-found')
  const { witness } = report.outcome
  assert.equal(witness.label, 'property-failure')
  const [x, y] = (witness.shrunk ?? witness.first).holes.map(hole => BigInt(hole.value.int))
  assert.ok(x > y, `${x} > ${y}`)
  assert.deepEqual(report['engine-defects'], [])
  // The report is a function of the specification: a second call gives the same bytes.
  assert.equal(runFuzzCampaign(impCampaign()).json, json)
})

test('throws for a malformed campaign specification', () => {
  assert.throws(
    () => runFuzzCampaign(impCampaign({ options: { 'max-dept': 3 } })),
    /campaign\.options: unknown field `max-dept`/,
  )
  assert.throws(() => runFuzzCampaign(impCampaign({ seed: 7 })), /invalid type/)
})

const readCoin = name =>
  fs.readFileSync(path.join(__dirname, '../../k-rust-fuzz/tests/data/coin', name), 'utf8')
// k-rust's build identity: its version and the digest of the sources it was built from.
const BUILD_IDENTITY = /^\d+\.\d+\.\d+(-[0-9A-Za-z.-]+)?\+src\.[0-9a-f]{32}$/
// The campaign thread's stack, which the report records, as krust fuzz's.
const STACK_SIZE = '268435456'

test('runs the campaign on its own thread and refuses a caller stack size', () => {
  assert.equal(runFuzzCampaign(impCampaign({ budget: { cases: '1' } })).report.identity['thread-stack-size'], STACK_SIZE)
  assert.throws(
    () => runFuzzCampaign(impCampaign({ identity: { 'k-rust-revision': 'r', 'thread-stack-size': 1 } })),
    /campaign\.identity\.thread-stack-size: the campaign runs on a thread of this binding/,
  )
})

// The differential campaign of the fuzz crate's own test: COIN against COIN-KILL, which adds the
// end N + 2 for N > 10, over the `3` of `flip(3)`.
const coinCampaign = () => ({
  definition: readCoin('coin.k'),
  moduleName: 'COIN',
  sourceName: 'coin.k',
  includePrelude: true,
  mutant: { definition: readCoin('coin-kill.k'), moduleName: 'COIN', sourceName: 'coin-kill.k', includePrelude: true },
  campaign: {
    program: { program: { name: 'flip.pgm', text: readCoin('flip.pgm'), 'start-sort': 'Pgm' }, 'config-vars': [] },
    holes: [{ name: 'N', sort: 'Int', location: { kind: 'span', program: 'flip.pgm', find: '3', literal: '3' } }],
    target: { kind: { kind: 'differential' }, 'run-to-completion': false, 'negated-property': false },
    proposers: { explicit: [{ N: { int: '10' } }] },
    seed: '7',
    identity: { 'k-rust-revision': 'binding-test' },
    budget: { cases: '64' },
  },
})

test('runs one differential fuzz campaign that kills a mutant', () => {
  const { report } = runFuzzCampaign(coinCampaign())
  assert.equal(report.identity.definitions.length, 2)
  assert.equal(report.outcome.status, 'witness-found')
  const { witness } = report.outcome
  const killing = witness.shrunk ?? witness.first
  assert.equal(killing.kill, 'added-end')
  assert.ok(BigInt(killing.holes[0].value.int) > 10n, killing.holes[0].value.int)
})

test('refuses a misspelt field inside a hole', () => {
  const options = impCampaign()
  options.campaign.holes[0].constraint = { range: { min: '0', max: '0' } }
  assert.throws(() => runFuzzCampaign(options), /unknown field `constraint`/)
})

test('refuses a misspelt option beside the campaign and in the mutant', () => {
  const options = impCampaign()
  options.syntaxModul = 'IMP-SYNTAX'
  assert.throws(() => runFuzzCampaign(options), /unknown field `syntaxModul`/)
  const coin = coinCampaign()
  coin.mutant.includePrelud = true
  assert.throws(() => runFuzzCampaign(coin), /unknown field `includePrelud`/)
})

test('names this build when the campaign gives no identity', () => {
  const options = impCampaign({ budget: { cases: '1' } })
  delete options.campaign.identity
  const { report } = runFuzzCampaign(options)
  assert.match(report.identity['k-rust-revision'], BUILD_IDENTITY)
  assert.equal(report.identity['thread-stack-size'], STACK_SIZE)
})
