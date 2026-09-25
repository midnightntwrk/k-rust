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

// Without associativity or priorities, a+a+a has two well-sorted trees that denote different terms,
// so no sort decision can pick one: the error must name the ambiguity and list both readings.
const bothAdditionReadings =
  /Parsing ambiguity\.[\s\S]*add\(a\(\.KList\),add\(a\(\.KList\),a\(\.KList\)\)\)[\s\S]*add\(add\(a\(\.KList\),a\(\.KList\)\),a\(\.KList\)\)/

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
        syntax Int ::= r"[0-9]+" [token]
        syntax Box ::= "box(" Int ")" [function, symbol(box)]
        syntax {S} S ::= "same(" S ")" [symbol(same)]
        rule box(same(1)) => box(1)
      endmodule
    `,
    moduleName: 'MAIN',
  })
  assert.match(compiled.definitionKore, /Lblsame/)
  assert.deepEqual(compiled.diagnostics, [])
})

test('reports both readings of an ambiguous rule', () => {
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
    bothAdditionReadings,
  )
})

test('reports the compiler MPFR folding boundary', () => {
  assert.throws(
    () =>
      compileDefinition({
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

test('reports both readings of an ambiguous program', () => {
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
    bothAdditionReadings,
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

  assert.throws(() => backend.search({ state: a, schemaVersion: 99 }), /schema version 99/)
  assert.throws(() => backend.search({ state: a, maxDeph: 1 }), /unknown field.*maxDeph/i)
  backend.free()
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
