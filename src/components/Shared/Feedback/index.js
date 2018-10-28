import React from 'react'
import cx from 'classnames'
import styles from './styles.scss'

const Feedback = ({ z3 }) =>
  z3 &&
  <div className={cx(styles.feedback, {
    [styles.error]: z3 !== 'unsat'
  })}>
  {
    (z3 === 'sat' ? "Your proof is incorrect" :
      (
        z3 === 'unsat' ? "Your proof is correct, well done!" :
        "There are errors in your proof"
      )
    )
  }
  </div>

export default Feedback