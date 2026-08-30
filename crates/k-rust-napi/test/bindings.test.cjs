const assert = require('node:assert/strict')
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
} = require('../dist/index.js')

const backendDefinition = String.raw`[]
module MAIN
  sort SortS{} []
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

test('uses Z3-backed parametric sort inference', () => {
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

  assert.equal(parsed.text, 'box(same{Int}(#token("1","Int")))')
})

test('compiles definitions through the full native pipeline', () => {
  const compiled = compileDefinition({
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
  })

  assert.match(compiled.definitionKore, /module MAIN/)
  assert.match(compiled.definitionKore, /Lblsame/)
  assert.match(compiled.syntaxDefinitionKore, /module MAIN/)
  assert.equal(compiled.macrosKore, '\n')
})

test('round-trips KAST and KORE through typed JSON', () => {
  const kast = parseKast('#token("x","Id")')
  assert.equal(printKast(kast.kast), kast.text)

  const kore = parseKore('X:S')
  assert.equal(printKore(kore.kore), kore.text)
})

test('runs the complete persistent native backend API', () => {
  const backend = createBackend({ definitionKore: backendDefinition, moduleName: 'MAIN' })
  const a = parseKore('a{}()').kore
  const c = parseKore('c{}()').kore

  assert.equal(backend.capabilities.smt, true)
  const execution = backend.execute({ state: a, maxDepth: 2 })
  assert.equal(printKore(execution.leaves[0].state), 'c{}()')
  assert.equal(printKore(backend.simplify({ state: a })), 'a{}()')
  assert.equal(backend.implies({ antecedent: c, consequent: c }).status, 'valid')
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

  assert.throws(() => backend.search({ state: a, schemaVersion: 99 }), /schema version 99/)
  assert.throws(() => backend.search({ state: a, maxDeph: 1 }), /unknown field.*maxDeph/i)
})

test('compileBackend compiles and creates a native session', () => {
  const backend = compileBackend({
    definition: `module MAIN
      syntax State ::= "a" [symbol(a)]
    endmodule`,
    moduleName: 'MAIN',
    includePrelude: false,
  })
  assert.equal(backend.capabilities.execution, true)
  assert.equal(backend.capabilities.smt, true)
})
