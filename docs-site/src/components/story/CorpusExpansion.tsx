'use client'

import type { ReactNode } from 'react'
import { Stage, type Player, usePlayer } from './player'
import shared from './MutateTheSpec.module.css'
import styles from './CorpusExpansion.module.css'

// The storage-language examples and combined strength index are illustrative.
// The index counts a caught mutation or an exercised pattern target as one goal.
// Event-pattern notation for the illustration; ellipses allow intervening events.
const pattern = `Write(addr, new)
    …
Invalidate(addr)
    …
Read(addr, new)`
const program = `write(7, 42);
work();
invalidate(key);
read(7);`

type ExpansionProps = {
  player: Player
  actor: string
  activity: string
  title: string
  children: ReactNode
  verdict: string
  caption: string
  count: number
  added: boolean
  confirmed: boolean
  result: string
  checking: boolean
  mode: 'match' | 'replay'
  footer: ReactNode
}

function Expansion({ player, actor, activity, title, children, verdict, caption, count, added, confirmed, result, checking, mode, footer }: ExpansionProps) {
  return (
    <Stage player={player} caption={caption}>
      <div>
      <div className={shared.agent}>
        <span className={shared.avatar} aria-hidden="true">{actor === 'AI agent' ? 'AI' : 'KRS'}</span>
        <div className={shared.agentCopy}><strong>{actor}</strong><div className={shared.activity} aria-live="polite">{activity}</div></div>
      </div>
      {mode === 'match' && (
        <>
          <svg className={shared.connections} viewBox="0 0 700 66" aria-hidden="true">
            <defs><marker id="pattern-agent-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto"><path d="M 0 0 L 10 5 L 0 10 z" /></marker></defs>
            <path className={player.at === 0 ? shared.activeConnection : undefined} d="M 340 2 V 20 H 170 V 64" markerEnd="url(#pattern-agent-arrow)" />
            <path className={checking ? shared.activeConnection : undefined} d="M 360 2 V 20 H 545 V 64" markerEnd="url(#pattern-agent-arrow)" />
            <text x="170" y="13" textAnchor="middle">AI writes pattern</text>
            <text x="545" y="13" textAnchor="middle">AI ensures pattern appears in corpus</text>
          </svg>
          <div className={shared.mobileFlow}>AI writes pattern → checks corpus → adds a test if missing</div>
        </>
      )}
      </div>
      <div className={styles.comparison}>
        <div className={shared.spec}>
          <div className={shared.heading}>{title}</div>
          {children}
          <div className={shared.verdict}>{verdict}</div>
        </div>
        <div key={`${mode}-${player.at}`} className={`${styles.bridge} ${checking && !confirmed ? styles.checking : ''}`} aria-label={mode === 'match' ? 'Check this pattern against every test execution' : 'Replay the found input before adding its test'}>
          <svg viewBox="0 0 48 20" aria-hidden="true"><path d="M 2 10 H 44 M 37 4 L 44 10 L 37 16" /><circle cx="4" cy="10" r="3" /></svg>
          <span>{mode}</span>
        </div>
        <div className={shared.corpus}>
          <div className={shared.heading}>Test corpus <span>100% rule coverage</span></div>
          <ol className={shared.tests}>
            {Array.from({ length: count }, (_, index) => (
              <li key={`${index}-${checking}`} className={checking && mode === 'match' ? styles.scan : undefined} style={{ animationDelay: `${index * 200}ms` }}>
                <code>test {index + 1}</code><span>{mode === 'match' ? checking ? 'pattern absent' : 'not checked' : 'target absent'}</span>
              </li>
            ))}
            <li className={`${shared.newTest} ${added ? shared.visible : ''}`} aria-hidden={!added}>
              <code>test {count + 1} <span>NEW</span></code>
              <span className={confirmed ? shared.caught : undefined}>{confirmed ? `✓ ${result}` : 'checking…'}</span>
            </li>
          </ol>
        </div>
      </div>
      {footer}
    </Stage>
  )
}

const patternPhases = [
  { activity: 'Proposes a pattern worth including in the corpus.', caption: 'Write a value, invalidate the same address, then read back the new value. Other events can occur between the operations we match.' },
  { activity: 'Checks every existing test execution for a match.', caption: 'Search each test’s execution for the pattern, keeping the address and value bindings across the matched events. No existing test exercises it.' },
  { activity: 'Adds a test for the missing cache interaction.', caption: 'AI adds a test that writes, invalidates, and reads back the new value. Run it and check the execution against the pattern.' },
  { activity: 'Keeps the matching test and proposes the next pattern.', caption: 'The new test exercises the chosen pattern. Keep it in the corpus, then use the next missing pattern to guide the next improvement.' },
]

export function InteractionPatterns() {
  const player = usePlayer(patternPhases.length, 2000)
  const checking = player.at >= 1
  const added = player.at >= 2
  const confirmed = player.at >= 3
  return (
    <Expansion player={player} actor="AI agent" activity={patternPhases[player.at].activity} title="Trace pattern · cache invalidation" verdict={confirmed ? '✓ New test matches the whole pattern' : checking ? 'No existing test matches the whole pattern' : 'Match the same address and new value'} caption={patternPhases[player.at].caption} count={4} added={added} confirmed={confirmed} checking={checking} mode="match" result="pattern matched" footer={
      <div className={shared.climb}>
        <div className={shared.score}><strong>Strength index · {confirmed ? 200 : 150}% of baseline</strong><span>3 mutations caught · {confirmed ? '1 pattern target' : '0 pattern targets'} exercised</span></div>
        <div className={shared.track} role="img" aria-label={`Illustrative strength index: ${confirmed ? 200 : 150}% of baseline`}>
          <div className={shared.fill} style={{ width: `${confirmed ? 80 : 60}%` }} />
          <span className={shared.baseline} style={{ left: '40%' }} />
        </div>
        <div className={shared.legend}><span>Illustrative index: mutation checks + pattern targets</span><span>AI proposes · measures · improves</span></div>
      </div>
    }>
      <pre><code>{pattern}</code></pre>
      <div className={styles.note}>… allows intervening events. <code>addr</code> and <code>new</code> keep the same values across matches.</div>
    </Expansion>
  )
}

const fuzzPhases = [
  { activity: 'Targets the cache interaction at an untested address.', caption: 'The corpus exercises the general cache pattern. Now target the interaction at address 7, which its existing tests do not exercise.' },
  { activity: 'Searches inputs that make the execution match.', caption: 'KRS searches key values using the specification. Invalidating key 0 or 3 misses the pattern: the write and read use address 7.' },
  { activity: 'Replays key = 7 to check the pattern again.', caption: 'With key = 7, the invalidation matches the address written and read. A fresh run confirms the read returns the new value, 42.' },
  { activity: 'Keeps the input that reaches the additional target.', caption: 'Add the confirmed input to the corpus: another target exercised, another improvement measured. KRS searches the inputs and replay confirms the result.' },
]

export function TargetedFuzzing() {
  const player = usePlayer(fuzzPhases.length, 2000)
  const searching = player.at >= 1
  const found = player.at >= 2
  const confirmed = player.at >= 3
  return (
    <Expansion player={player} actor="Targeted fuzzer" activity={fuzzPhases[player.at].activity} title="Fixed program · input hole: key" verdict={confirmed ? '✓ Replay confirms the pattern' : found ? 'Candidate found: key = 7' : searching ? 'Search input values; keep the program fixed' : 'Target: cache pattern at address 7'} caption={fuzzPhases[player.at].caption} count={5} added={found} confirmed={confirmed} checking={searching} mode="replay" result="pattern confirmed" footer={
      <div className={shared.climb}>
        <div className={shared.score}><strong>Strength index · {confirmed ? 250 : 200}% of baseline</strong><span>{confirmed ? '1 additional fuzz target reached' : 'Additional fuzz target not yet reached'}</span></div>
        <div className={shared.track} role="img" aria-label={`Illustrative strength index: ${confirmed ? 250 : 200}% of baseline`}>
          <div className={shared.fill} style={{ width: `${confirmed ? 100 : 80}%` }} />
          <span className={shared.baseline} style={{ left: '40%' }} />
        </div>
        <div className={shared.legend}><span>Illustrative index: mutation checks + pattern targets</span><span>Fixed seed + work budget · replay witnesses</span></div>
      </div>
    }>
      <pre><code>{program}</code></pre>
      <div className={styles.candidates}>
        <span>key</span>
        <code className={searching ? styles.tried : undefined}>0</code>
        <code className={searching ? styles.tried : undefined}>3</code>
        <code className={found ? styles.hit : undefined}>7 {found ? '✓ target reached' : ''}</code>
      </div>
      <div className={styles.note}>Illustrative cache program; address 7 starts cached.</div>
    </Expansion>
  )
}
