import assert from 'node:assert/strict'
import { createHash } from 'node:crypto'
import { readFileSync } from 'node:fs'
import test from 'node:test'

import {
  compileBackend,
  compileDefinition,
  createBackend,
  default as init,
  formatKoreDefinition,
  parseKast,
  parseKore,
  parseProgram,
  printKast,
  printKore,
  runFuzzCampaign,
} from '../dist/index.js'

const bytes = readFileSync(new URL('../generated/bindings_bg.wasm', import.meta.url))
await init(bytes)

const backendDefinition = String.raw`[]
module MAIN
  sort SortS{} []
  alias weakExistsFinally{A}(A) : A where weakExistsFinally{A}(@X:A) := @X:A []
  symbol a{}() : SortS{} [constructor{}()]
  symbol b{}() : SortS{} [constructor{}()]
  symbol c{}() : SortS{} [constructor{}()]
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

test('exposes a simplification budget diagnostic on its execution leaf', () => {
  const definitionKore = readFileSync(
    new URL('../../k-rust/tests/fixtures/execution-budget.kore', import.meta.url),
    'utf8',
  )
  const backend = createBackend({ definitionKore, moduleName: 'MAIN' })
  const leaf = backend.execute({ state: parseKore('start{}()').kore, maxSimplificationIterations: 3 }).leaves[0]
  assert.deepEqual(leaf.diagnostics, [
    { kind: 'simplification-budget-exhausted', limit: 3, subject: 'term' },
  ])
})

test('exposes the diagnostic on only the branch candidate that emitted it', () => {
  const definitionKore = readFileSync(
    new URL('../../k-rust/tests/fixtures/execution-candidates.kore', import.meta.url),
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
  const definitionKore = readFileSync(
    new URL('../../k-rust/tests/fixtures/search-diagnostics.kore', import.meta.url),
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

test('exposes the compiled rule catalog', () => {
  const backend = createBackend({ definitionKore: backendDefinition, moduleName: 'MAIN' })
  try {
    const catalog = backend.ruleCatalog()
    assert.deepEqual(backend.ruleCatalog('MAIN'), catalog)
    assert.deepEqual(
      catalog.filter((rule) => rule.kind === 'rewrite').map((rule) => rule.label),
      ['a-to-b', 'b-to-c'],
    )
    assert.ok(catalog.every((rule) => typeof rule.id === 'string'))
    assert.ok(catalog.every((rule) => Array.isArray(rule.origins)))
    assert.ok(catalog.every((rule) => typeof rule.sharedIdentity === 'boolean'))
  } finally {
    backend.free()
  }
})

// Without associativity or priorities, a+a+a has two well-sorted trees that denote different terms,
// add(a, add(a, a)) and add(add(a, a), a), so no sort decision can pick one. Both are rooted at
// add and differ at its two operands together, so the error names the ambiguity by those two
// subterms, each at its first character, with the readings each takes: a or add(a, a).
const additionAmbiguity = (prefix, first, second) => ({
  name: 'Error',
  message:
    `${prefix}Parsing ambiguity: the readings differ in 2 subterms.\n` +
    [first, second]
      .map(
        (at, index) =>
          `Subterm ${index + 1} at ${at}:\n` +
          '1: syntax Exp ::= "a" [symbol(a)]\n' +
          '    a(.KList)\n' +
          '2: syntax Exp ::= Exp "+" Exp [symbol(add)]\n' +
          '    add(a(.KList),a(.KList))',
      )
      .join('\n'),
})

test('compiles a portable definition into all KORE artifacts', () => {
  const compiled = compileDefinition({
    definition: `
      module MAIN
        syntax Int ::= r"[0-9]+" [token]
      endmodule
    `,
    moduleName: 'MAIN',
  })

  assert.match(compiled.definitionKore, /module MAIN/)
  assert.match(compiled.syntaxDefinitionKore, /module MAIN/)
  assert.equal(compiled.macrosKore, '\n')
  assert.deepEqual(compiled.diagnostics, [])
})

test('compiles unambiguous parametric applications portably', () => {
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
  })
  assert.match(compiled.definitionKore, /Lblsame/)
  assert.deepEqual(compiled.diagnostics, [])
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
      }),
    /the instance of `same`.*is at sort Int/,
  )
})

test('reports an ambiguous rule by the two subterms its readings differ in', () => {
  assert.throws(
    () =>
      compileDefinition({
        definition: `
          module MAIN
            syntax Exp ::= "a" [symbol(a)] | Exp "+" Exp [symbol(add)]
            rule a+a+a => a
          endmodule
        `,
        moduleName: 'MAIN',
      }),
    additionAmbiguity('definition.k:4:18: could not parse rule in module "MAIN": ', '4:18', '4:20'),
  )
})

test('folds binary64 Float constants in the portable build', () => {
  // The constant fold computes a FLOAT application through the backend's evaluation entry in
  // every build, so the portable package writes the value a run computes: 0.1 + 0.2 in binary64.
  const compiled = compileDefinition({
    definition: String.raw`
      module MAIN
        syntax Float [hook(FLOAT.Float)]
        syntax Float ::= r"[0-9]+\\.[0-9]+" [token]
        syntax Float ::= "add(" Float "," Float ")" [function, hook(FLOAT.add), symbol(addFloat)]
        syntax Float ::= "result" [function, symbol(result)]
        rule result => add(0.1, 0.2)
      endmodule
    `,
    moduleName: 'MAIN',
  })
  assert.deepEqual(compiled.diagnostics, [])
  // The function rule's right-hand side, as the equation `result() = 3.0000000000000004e-01`.
  const rule = compiled.definitionKore.match(
    /\\equals\{SortFloat\{\},\s*R\}\(\s*Lblresult\{\}\(\),[^]*?\)\s*\)\s*\[/,
  )
  assert.ok(rule, 'the rule for result is emitted')
  assert.match(rule[0], /\\dv\{SortFloat\{\}\}\("3\.0000000000000004e-01p53x11"\)/)
  assert.doesNotMatch(rule[0], /LbladdFloat/)
})

test('executes the portable parser inside WebAssembly', () => {
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
  })

  assert.equal(parsed.text, '#token("42","Int")')
  assert.equal(parsed.kast.term.node, 'KToken')
  assert.equal(parsed.kast.term.token, '42')
})

test('presents inferred parametric labels like reference kast', () => {
  const parsed = parseProgram({
    definition: `
      module MAIN
        syntax Int ::= r"[0-9]+" [token]
        syntax K ::= Int
        syntax {S} Int ::= "take(" S ")" [function, symbol(take)]
      endmodule
    `,
    moduleName: 'MAIN',
    sort: 'Int',
    program: 'take(1)',
    includePrelude: false,
  })

  assert.equal(parsed.text, 'take(#token("1","Int"))')
  assert.deepEqual(parsed.kast.term.label.params, [])
})

test('infers nested parametric applications portably', () => {
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

test('reports an ambiguous program by the two subterms its readings differ in', () => {
  assert.throws(
    () =>
      parseProgram({
        definition: `
          module MAIN
            syntax Exp ::= "a" [symbol(a)] | Exp "+" Exp [symbol(add)]
          endmodule
        `,
        moduleName: 'MAIN',
        sort: 'Exp',
        program: 'a+a+a',
        includePrelude: false,
      }),
    additionAmbiguity('could not parse program as Exp with module "MAIN": ', '1:1', '1:3'),
  )
})

test('parses a program with the embedded prelude', () => {
  const parsed = parseProgram({
    definition: `
      module MAIN
        imports INT
        syntax Exp ::= Int | Exp "+" Exp [symbol(plus)]
      endmodule
    `,
    moduleName: 'MAIN',
    sort: 'Exp',
    program: '1 + 2',
    includePrelude: true,
  })
  assert.equal(parsed.text, 'plus(#token("1","Int"),#token("2","Int"))')
})

test('compiles a definition importing the embedded prelude to the native definition.kore', () => {
  // Shared with the Rust tests in src/lib.rs, which assert the same digests natively.
  const fixture = JSON.parse(
    readFileSync(new URL('./fixtures/prelude-int.json', import.meta.url), 'utf8'),
  )
  for (const backend of ['rust', 'llvm']) {
    const compiled = compileDefinition({
      definition: fixture.definition,
      moduleName: fixture.moduleName,
      backend,
      includePrelude: true,
    })
    const digest = createHash('sha256').update(compiled.definitionKore).digest('hex')
    assert.equal(digest, fixture.definitionKoreSha256[backend], backend)
  }
})

test('round-trips KAST and KORE through typed JSON', () => {
  const kast = parseKast('#token("x","Id")')
  assert.equal(printKast(kast.kast), kast.text)

  const kore = parseKore('X:S')
  assert.equal(printKore(kore.kore), kore.text)

  assert.match(
    formatKoreDefinition('[] module TEST sort S{} [] endmodule []'),
    /module TEST[\s\S]*sort S\{\}/,
  )
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

test('runs portable backend operations and reports the SMT boundary', () => {
  const backend = createBackend({ definitionKore: backendDefinition, moduleName: 'MAIN' })
  const a = parseKore('a{}()').kore
  const c = parseKore('c{}()').kore

  assert.equal(backend.capabilities.smt, false)
  assert.equal(printKore(backend.execute({ state: a, maxDepth: 2 }).leaves[0].state), 'c{}()')
  assert.equal(printKore(backend.simplify({ state: a })), 'a{}()')
  const implication = backend.implies({ antecedent: c, consequent: c })
  assert.equal(implication.schemaVersion, 2)
  assert.equal(implication.status, 'valid')
  assert.equal(printKore(implication.condition.predicate), '\\top{SortS{}}()')
  assert.equal(printKore(implication.condition.substitution), '\\top{SortS{}}()')
  assert.equal(printKore(implication.condition.witnesses), '\\top{SortS{}}()')
  assert.equal(backend.prove({ claim: 'reaches-c' }).status, 'proven')
  assert.throws(
    () => backend.getModel({ state: parseKore('\\top{SortS{}}()').kore }),
    /no Z3|SMT-enabled native build/i,
  )
  assert.throws(
    () => backend.execute({ state: a, stepTimeoutMs: 10 }),
    /monotonic clock|step timeouts/i,
  )
  backend.free()
})

test('searches and observes the persistent portable backend graph', () => {
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
  assert.equal(backend.capabilities.smtUnknowns, true)
  assert.equal(backend.execute({ state: a }).coverage, undefined)
  assert.deepEqual(backend.execute({ state: a, collectCoverage: true }).coverage, {
    applied: ['a-to-b', 'b-to-c'],
    matched: ['a-to-b', 'b-to-c'],
  })

  assert.throws(() => backend.search({ state: a, schemaVersion: 99 }), /schema version 99/)
  assert.throws(() => backend.search({ state: a, maxDeph: 1 }), /unknown field.*maxDeph/i)
  backend.free()
})

// Rust's default 1 MiB wasm32 stack traps on this program from about 920 levels when it is
// parsed in the dev module CI tests (960 in a release one); the module's 8 MiB stack holds the
// depth below, which stays under the engine's own call-stack limit at Node's default (about
// 1,800 levels). Simplification is not tested here: in the dev module the engine's call stack
// binds it at about 390 nested calls whatever the linear stack. docs/backend-port.md, "Stack
// bounds".
test('parses a program deeper than a 1 MiB stack holds', () => {
  const definition = `
    module TICKS
      syntax Pgm ::= "tick" Pgm [function, symbol(tick)] | "done" [symbol(done)]
      rule tick P => P
    endmodule
  `
  const statements = 1400
  const parsed = parseProgram({
    definition,
    moduleName: 'TICKS',
    sort: 'Pgm',
    program: `${'tick '.repeat(statements)}done`,
    includePrelude: false,
  })
  let term = parsed.kast.term
  let ticks = 0
  while (term.label.name === 'tick') {
    ticks += 1
    term = term.args[0]
  }
  assert.equal(ticks, statements)
  assert.equal(term.label.name, 'done')
})

test('compileBackend compiles and creates a portable session', () => {
  const backend = compileBackend({
    definition: `module MAIN
      syntax State ::= "a" [function, symbol(a)] | "b" [symbol(b)]
      rule a => b
    endmodule`,
    moduleName: 'MAIN',
    includePrelude: false,
  })
  assert.equal(backend.capabilities.execution, true)
  assert.equal(backend.capabilities.smt, false)
  assert.equal(printKore(backend.simplify({ state: parseKore('Lbla{}()').kore })), 'Lblb{}()')
  backend.free()
})

const readFixture = name =>
  readFileSync(new URL(`../../k-rust-fuzz/tests/data/imp/${name}`, import.meta.url), 'utf8')
const SOLVER = 'none'

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

test('refuses the safety limit and the solve proposer before compiling anything', () => {
  const unparsable = options => ({ ...options, definition: 'not a definition' })
  assert.throws(
    () => runFuzzCampaign(unparsable(impCampaign({ options: { 'safety-limit-ms': 1000 } }))),
    /^Error: campaign\.options\.safety-limit-ms: the per-case safety limit is not available in WebAssembly/,
  )
  assert.throws(
    () => runFuzzCampaign(unparsable(impCampaign({ proposers: { weights: { blind: 1, solve: 1 } } }))),
    /^Error: campaign\.proposers\.weights\.solve: the solve proposer is not available in WebAssembly/,
  )
})

const readCoin = name =>
  readFileSync(new URL(`../../k-rust-fuzz/tests/data/coin/${name}`, import.meta.url), 'utf8')
// k-rust's build identity: its version and the digest of the sources it was built from.
const BUILD_IDENTITY = /^\d+\.\d+\.\d+(-[0-9A-Za-z.-]+)?\+src\.[0-9a-f]{32}$/
const STACK_SIZE = null

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
