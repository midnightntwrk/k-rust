const assert = require('node:assert/strict')
const test = require('node:test')

const {
  compileDefinition,
  parseKast,
  parseKore,
  parseProgram,
  printKast,
  printKore,
} = require('../dist/index.js')

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
