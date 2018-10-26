import React from 'react'
import cx from 'classnames'
import styles from './styles.scss'

const Feedback = ({ z3, steps }) =>
  z3 &&
  <div className={cx(styles.feedback, {
    [styles.error]: z3 !== 'unsat'
  })}>
  {
    steps.length <= 1 ? "Please enter more than one step to validate your proof" :
    (z3 === 'sat' ? "Your proof is incorrect" :
      (
        z3 === 'unsat' ? "Your proof is correct, well done!" :
        "There are errors in your proof"
      )
    )
  }
  </div>

export default Feedback