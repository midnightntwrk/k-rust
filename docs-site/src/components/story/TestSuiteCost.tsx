'use client'

import { Stage, Status, usePlayer } from './player'
import glass from './TestSuiteCost.module.css'

const phases = [
  { count: 1, caption: 'One meaningless test is easy to overlook.' },
  { count: 4, caption: 'Keep asking AI for tests, and these assertions start to pile up.' },
  { count: 8, caption: 'They still have to compile and run on every change. Slower feedback for developers. More CI budget spent. No additional confidence in the code.' },
]

export function TestSuiteCost() {
  const player = usePlayer(phases.length, 2500)
  const phase = phases[player.at]
  return (
    <Stage player={player} caption={phase.caption} aside={<Status kind="illustrative">illustrative suite</Status>}>
      <svg
        className={glass.stack}
        viewBox="0 0 400 250"
        role="img"
        aria-label={`${phase.count} test panes, each showing code marks and a green pass check, piled onto a labeled test machine${phase.count === 8 ? ', with the test machine bending and cracking under the weight' : ''}`}
      >
        <path className={glass.ground} d="M48 222H352" />
        <path className={glass.support} d="M80 199H104V222H80Z M296 199H320V222H296Z" />
        {Array.from({ length: phase.count + 1 }, (_, index) => (
          <g key={index} transform={`translate(${[0, 2, -2, 1, -3, 2, -1, 0, 1][index]} ${175 - index * 20})`}>
            <g className={glass.pane} style={{ animationDelay: `${index * 90}ms` }}>
              <path
                className={`${glass.sheet} ${index === 0 ? glass.machine : ''}`}
                d={index === 0 && phase.count === 8
                  ? 'M64 0Q200 14 336 0V24Q200 38 64 24Z'
                  : index === 0 ? 'M64 0H336V24H64Z' : 'M64 0H336V20H64Z'}
              />
              <g transform={index === 0 && phase.count === 8 ? 'translate(0 3)' : undefined}>
                {index === 0 ? (
                  <>
                    <text className={glass.machineLabel} x="82" y="16">test machine</text>
                    <path className={glass.code} d="M294 9V15 M301 9V15 M308 9V15 M315 9V15" />
                  </>
                ) : (
                  <>
                    <path className={glass.code} d="M86 8L82 12L86 16 M96 8L100 12L96 16 M92 7L90 17 M114 9H147 M155 9H179 M122 15H168" />
                    <circle className={glass.passBadge} cx="315" cy="12" r="7" />
                    <path className={glass.passCheck} d="M311.5 12L314 14.5L318.5 9.5" />
                  </>
                )}
              </g>
              {index === 0 && phase.count === 8 && (
                <path className={glass.crack} d="M193 7L201 15L195 23L207 31 M201 15L213 12 M195 23L185 26" />
              )}
            </g>
          </g>
        ))}
      </svg>
    </Stage>
  )
}
