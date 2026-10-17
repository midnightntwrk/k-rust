// The table both mutation scenes share: tests down, edits across, each cell the result krs
// recorded for that test under that edit.

import { caught, mutations, result, type Test } from './data'
import styles from './Story.module.css'

export type MatrixState = {
  rows: readonly Test[]
  /** Indices into `mutations` of the columns shown. */
  columns: readonly number[]
  /** Per column, how many rows have been run. */
  run: Readonly<Record<number, number>>
  verdict?: boolean
  fresh?: string
  /** Per column, the test cached as the one that catches it. */
  killers?: Readonly<Record<number, string>>
  unused?: readonly string[]
}

export const survives = (column: number, rows: readonly Test[]) => !rows.some((test) => caught(mutations[column], test))

export function MutationMatrix({ state }: { state: MatrixState }) {
  return (
    <div className={styles.tableWrap}>
      <table className={styles.table} style={{ minWidth: '32rem' }}>
        <thead>
          <tr>
            <th>test</th>
            <th>specification says</th>
            {state.columns.map((column) => (
              <th key={column}>
                edit {mutations[column].id.toUpperCase()}
                <span className={styles.mono}>{mutations[column].label}</span>
              </th>
            ))}
          </tr>
        </thead>
        <tbody>
          {state.rows.map((test, row) => (
            <tr
              key={test.id}
              className={state.fresh === test.id ? styles.fresh : state.unused?.includes(test.id) ? styles.unused : undefined}
            >
              <td>
                {test.id} · {test.program}
              </td>
              <td>{result('base', test.id)}</td>
              {state.columns.map((column) => {
                if ((state.run[column] ?? 0) <= row) {
                  return (
                    <td key={column}>
                      <span className={`${styles.pill} ${styles.idle}`}>not run</span>
                    </td>
                  )
                }
                const hit = caught(mutations[column], test)
                const cached = state.killers?.[column] === test.id
                return (
                  <td key={column}>
                    <span className={`${styles.pill} ${hit ? styles.pass : styles.idle}`}>{hit ? (cached ? 'caught, cached' : 'caught') : 'same'}</span>
                    <span className={styles.result}>{result(mutations[column].id, test.id)}</span>
                  </td>
                )
              })}
            </tr>
          ))}
        </tbody>
        {state.verdict && (
          <tfoot>
            <tr>
              <td colSpan={2}>verdict</td>
              {state.columns.map((column) => (
                <td key={column}>
                  {(state.run[column] ?? 0) >= state.rows.length &&
                    (survives(column, state.rows) ? (
                      <span className={`${styles.pill} ${styles.missed}`}>survived</span>
                    ) : (
                      <span className={`${styles.pill} ${styles.pass}`}>caught</span>
                    ))}
                </td>
              ))}
            </tr>
          </tfoot>
        )}
      </table>
    </div>
  )
}
