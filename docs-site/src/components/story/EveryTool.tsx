'use client'

// Scene: one specification, every tool. Each tool gets a picture of what it does; what krs
// printed for it is one click away and comes from the recorded outputs.

import type { ReactNode } from 'react'

import { output, paperRules, result, ruleNames, tests } from './data'
import { authoredClaim, NativeProofResult } from './NativeClaims'
import { Controls, usePlayer } from './player'
import styles from './Story.module.css'
import visual from './SpecificationTools.module.css'

const program = tests.find((test) => test.id === 't3')!.program
const answer = result('base', 't3')
const kRules = output('story-emit-k')
  .split('\n')
  .filter((line) => line.startsWith('  rule '))
  .map((line) => line.trim().replace(/ \[label\([^)]*\)\]$/, ''))

function Raw({ id }: { id: string }) {
  return (
    <details className={styles.raw}>
      <summary>What krs printed</summary>
      <pre className={styles.panel}>{output(id).trimEnd()}</pre>
    </details>
  )
}

function Box({ x, y, label, result = false }: { x: number; y: number; label: string; result?: boolean }) {
  const width = Math.max(56, label.length * 8 + 18)
  return (
    <>
      <rect className={result ? styles.result : undefined} x={x - width / 2} y={y - 14} width={width} height={28} rx={6} />
      <text x={x} y={y + 4.5} textAnchor="middle">
        {label}
      </text>
    </>
  )
}

const tools: { verb: string; what: string; title: string; body: ReactNode }[] = [
  {
    verb: 'check',
    what: 'Is the specification well-formed?',
    title: 'The specification is checked before any tool uses it.',
    body: (
      <>
        <p>rustc checks names and types; KRS then checks what K needs, such as sorts lining up.</p>
        <Raw id="story-check" />
      </>
    ),
  },
  {
    verb: 'parse',
    what: 'Read a program into a term',
    title: "Text in the specification's own syntax becomes a tree.",
    body: (
      <>
        <svg viewBox="0 0 360 200" role="img" aria-label={`The parse tree of ${program}`}>
          <line x1={180} y1={32} x2={100} y2={88} />
          <line x1={180} y1={32} x2={260} y2={88} />
          <line x1={100} y1={102} x2={100} y2={156} />
          <line x1={260} y1={102} x2={260} y2={156} />
          <Box x={180} y={22} label="plus" />
          <Box x={100} y={95} label="s" />
          <Box x={260} y={95} label="s" />
          <Box x={100} y={168} label="zero" />
          <Box x={260} y={168} label="zero" />
        </svg>
        <Raw id="story-parse" />
      </>
    ),
  },
  {
    verb: 'run',
    what: 'Compute the answer',
    title: 'The specification computes the answer directly.',
    body: (
      <>
        <div className={styles.flow}>
          <span>{program}</span>
          <span aria-hidden="true">⟶</span>
          <span className={styles.answer}>{answer}</span>
        </div>
        <p>The rewrite machine you just saw performs these rule applications directly.</p>
        <Raw id="story-base-t3" />
      </>
    ),
  },
  {
    verb: 'search',
    what: 'Every possible answer, not just one',
    title: 'Search finds every result the specification allows.',
    body: (
      <>
        <svg viewBox="0 0 420 90" role="img" aria-label={`Search from ${program} finds one result, ${answer}`}>
          <line x1={212} y1={40} x2={282} y2={40} />
          <Box x={110} y={40} label={program} />
          <Box x={335} y={40} label={answer} result />
          <text className={styles.muted} x={335} y={78} textAnchor="middle">
            result 1 of 1
          </text>
        </svg>
        <p>For plus there is exactly one. In a language with real choices, such as concurrency, there can be many, and search finds them all.</p>
        <Raw id="story-search" />
      </>
    ),
  },
  {
    verb: 'symbolic execution',
    what: 'Explore unknown inputs',
    title: 'Explore paths without choosing every input in advance.',
    body: (
      <>
        <div className={styles.flow}>
          <code>plus(zero, N)</code>
          <span aria-hidden="true">⟶</span>
          <span className={styles.answer}>N</span>
        </div>
        <p>N stands for any natural number. Symbolic execution follows the specification’s rules with unknown inputs, tracking the conditions under which each path applies.</p>
        <p>Use it to explore which inputs can reach an error or a state you care about.</p>
      </>
    ),
  },
  {
    verb: 'prove',
    what: 'Check claims about behavior',
    title: 'Write k::claims!, then check it with krs prove.',
    body: (
      <>
        <pre className={styles.panel}>{authoredClaim}</pre>
        <p>This claim covers every natural number n. KRS checks it directly with symbolic execution; a concrete counterexample can guide a new test, while an unfinished proof remains inconclusive.</p>
        <NativeProofResult />
      </>
    ),
  },
  {
    verb: 'lean',
    what: 'Generate a Lean library',
    title: 'Take the same specification into Lean.',
    body: (
      <>
        <div className={visual.toolFlow}><strong>KRS specification</strong><span>→</span><strong>k2lean</strong><span>→</span><strong>Lean library</strong></div>
        <p>Generate Lean types, functions, execution rules, and supporting proofs. Bring K claims into Lean with k2lean claims; use its claim tactic or write your own proofs. Extend the model for properties such as type soundness or bisimulation.</p>
        <div className={visual.benefits}>
          <a href="https://github.com/midnightntwrk/k-rust/tree/main/k2lean/demos/claims">Program properties ↗</a>
          <a href="https://github.com/midnightntwrk/k-rust/tree/main/k2lean/demos/ImpTypes">Type soundness ↗</a>
          <a href="https://github.com/midnightntwrk/k-rust/tree/main/k2lean/demos/ImpRel">Bisimulation ↗</a>
        </div>
      </>
    ),
  },
  {
    verb: 'fuzz',
    what: 'Find inputs that reach a target',
    title: 'Choose a program and a target. Let the fuzzer craft the inputs.',
    body: (
      <>
        <div className={visual.toolFlow}><strong>Program + input holes</strong><span>→</span><strong>Targeted search</strong><span>→</span><strong>Replayable input</strong></div>
        <p>Find inputs that trigger a crash, reach a rule, or put the program in a state you specify. The fuzzer steers input values using the specification, then confirms a candidate by running it again.</p>
        <p>Keep the program you wrote; vary its inputs. The same mechanism can search for an input that makes two specifications disagree.</p>
        <a href="https://github.com/midnightntwrk/k-rust/tree/main/crates/k-rust-fuzz">Explore k-rust-fuzz ↗</a>
      </>
    ),
  },
  {
    verb: 'mutation testing',
    what: 'Measure what your tests catch',
    title: 'Would your tests notice a mistake in the specification?',
    body: (
      <>
        <div className={visual.toolFlow}><strong>Edit a rule</strong><span>→</span><strong>Run the corpus</strong><span>→</span><strong>Caught or missed?</strong></div>
        <p>Make a deliberate change to the specification and compare the test results. A changed result means the corpus caught the edit; an unchanged result can reveal a gap for the next test to close.</p>
        <a href="#mutation-testing-done-right">See how mutation testing guides the hill-climb ↓</a>
      </>
    ),
  },
  {
    verb: 'emit-k',
    what: 'The K definition underneath',
    title: 'Each rule is a K rule, readable as text.',
    body: (
      <>
        <pre className={styles.panel}>{kRules.join('\n')}</pre>
        <p>The last scene lines the Rust and the K up side by side. (Rule labels trimmed here.)</p>
      </>
    ),
  },
]

if (kRules.length !== ruleNames.length) throw new Error('story scene: the emitted K no longer has one rule per paper rule')

export function EveryTool() {
  const player = usePlayer(tools.length, 3600)
  const tool = tools[player.at]
  return (
    <div className={styles.stage}>
      <div className={styles.hub}>
        <div className={styles.panel}>
          <div className={styles.label}>the specification</div>
          {ruleNames.map((name) => (
            <div key={name} className={styles.mono}>
              {paperRules[name].lhs} = {paperRules[name].rhs}
            </div>
          ))}
          <div className={styles.label} style={{ marginTop: '0.5rem' }}>
            a program
          </div>
          <div className={styles.mono}>{program}</div>
        </div>
        <div className={styles.tools} role="group" aria-label="Tools from the specification">
          {tools.map((candidate, index) => (
            <button
              key={candidate.verb}
              type="button"
              className={styles.choice}
              aria-pressed={index === player.at}
              onClick={() => player.go(index)}
            >
              <span className={styles.verb}>{candidate.verb}</span>
              <span className={styles.what}>{candidate.what}</span>
            </button>
          ))}
        </div>
      </div>
      <div className={styles.view} aria-live="polite">
        <div className={styles.title}>{tool.title}</div>
        {tool.body}
      </div>
      <Controls player={player} step={false} reset={false} />
    </div>
  )
}
