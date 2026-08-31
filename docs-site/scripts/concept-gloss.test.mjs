#!/usr/bin/env node
import assert from 'node:assert/strict'
import { readFileSync } from 'node:fs'
import test from 'node:test'

const component = readFileSync(new URL('../src/components/ConceptGloss.tsx', import.meta.url), 'utf8')
const css = readFileSync(new URL('../src/components/ConceptGloss.module.css', import.meta.url), 'utf8')

test('gloss trigger is keyboard-navigable and names its tooltip', () => {
  assert.match(component, /<a[^>]+href=\{entry\.route\}[^>]+aria-describedby=\{tooltipId\}/s)
  assert.match(component, /id=\{tooltipId\} role="tooltip"/)
  assert.match(css, /\.root:focus-within \.tooltip/)
})

test('gloss remains inside a narrow viewport', () => {
  assert.match(css, /@media \(max-width: 40rem\)/)
  assert.match(css, /position: fixed/)
  assert.match(css, /inset-inline: 1rem/)
})

test('gloss honors reduced motion', () => {
  assert.match(css, /@media \(prefers-reduced-motion: reduce\)/)
  assert.match(css, /transition: none/)
})
