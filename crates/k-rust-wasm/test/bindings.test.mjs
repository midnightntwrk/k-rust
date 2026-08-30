import assert from 'node:assert/strict'
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
} from '../dist/index.js'

const bytes = readFileSync(new URL('../generated/bindings_bg.wasm', import.meta.url))
await init(bytes)

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

test('reports the compiler Z3 inference boundary', () => {
  assert.throws(
    () =>
      compileDefinition({
        definition: `
          module MAIN
            syntax Int ::= r"[0-9]+" [token]
            syntax Box ::= "box(" Int ")" [function, symbol(box)]
            syntax {S} S ::= "same(" S ")" [function, symbol(same)]
            rule box(same(1)) => box(1)
          endmodule
        `,
        moduleName: 'MAIN',
      }),
    /native Z3 sort inference/i,
  )
})

test('reports the compiler MPFR folding boundary', () => {
  assert.throws(
    () =>
      compileDefinition({
        definition: `
          module MAIN
            syntax Float [hook(FLOAT.Float)]
            syntax Float ::= r"[0-9]+\\.[0-9]+" [token]
            syntax Float ::= "add(" Float "," Float ")" [function, hook(FLOAT.add), symbol(addFloat)]
            syntax Float ::= "result" [function, symbol(result)]
            rule result => add(0.1, 0.2)
          endmodule
        `,
        moduleName: 'MAIN',
      }),
    /native MPFR implementation/i,
  )
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

test('reports the portable Z3 inference boundary', () => {
  assert.throws(
    () =>
      parseProgram({
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
      }),
    /native Z3 sort inference/i,
  )
})

test('rejects the native prelude with an actionable boundary error', () => {
  assert.throws(
    () =>
      parseProgram({
        definition: 'module MAIN\nendmodule',
        moduleName: 'MAIN',
        sort: 'K',
        program: '.K',
        includePrelude: true,
      }),
    /embedded prelude requires native Z3 inference/i,
  )
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

test('runs portable backend operations and reports the SMT boundary', () => {
  const backend = createBackend({ definitionKore: backendDefinition, moduleName: 'MAIN' })
  const a = parseKore('a{}()').kore
  const c = parseKore('c{}()').kore

  assert.equal(backend.capabilities.smt, false)
  assert.equal(printKore(backend.execute({ state: a, maxDepth: 2 }).leaves[0].state), 'c{}()')
  assert.equal(printKore(backend.simplify({ state: a })), 'a{}()')
  assert.equal(backend.implies({ antecedent: c, consequent: c }).status, 'valid')
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

  assert.throws(() => backend.search({ state: a, schemaVersion: 99 }), /schema version 99/)
  assert.throws(() => backend.search({ state: a, maxDeph: 1 }), /unknown field.*maxDeph/i)
  backend.free()
})

test('compileBackend compiles and creates a portable session', () => {
  const backend = compileBackend({
    definition: `module MAIN
      syntax State ::= "a" [symbol(a)]
    endmodule`,
    moduleName: 'MAIN',
    includePrelude: false,
  })
  assert.equal(backend.capabilities.execution, true)
  assert.equal(backend.capabilities.smt, false)
  backend.free()
})
