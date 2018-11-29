import React from 'react'
import styles from './styles.scss'

const LineNumber = ({ type, firstLineNumber = 0, index, parentCase, step: { ast } }) =>
  type !== 'goal' &&
  <div className={styles.lineNumber}>
    {firstLineNumber + index + 1} { parentCase && ast.type === 'assume' && "[Case " + parentCase + "]" }
  </div>

export default LineNumber