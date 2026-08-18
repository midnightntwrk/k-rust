import assert from 'node:assert/strict'
import { readFileSync } from 'node:fs'
import test from 'node:test'

import {
  compileDefinition,
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
