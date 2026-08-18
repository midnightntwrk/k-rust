import assert from 'node:assert/strict'
import { readFileSync } from 'node:fs'
import test from 'node:test'

import { initSync, parseKast } from '../dist/index.js'

const bytes = readFileSync(new URL('../generated/bindings_bg.wasm', import.meta.url))
initSync(bytes)

test('supports synchronous initialization from caller-provided bytes', () => {
  assert.equal(parseKast('#token("x","Id")').kast.term.node, 'KToken')
})
