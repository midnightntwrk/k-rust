import assert from 'node:assert/strict'
import test from 'node:test'

import { parseKast } from '../dist/index.js'

test('explains the required initialization step', () => {
  assert.throws(() => parseKast('#token("x","Id")'), /call init\(\) or initSync\(\) first/)
})
