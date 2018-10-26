import React, { Component } from 'react'
import cx from 'classnames'

import styles from './styles.scss'

class Feedback extends Component {
  getFeedbackText() {
    const { z3, steps } = this.props

    if (steps.length <= 1) {
      return "Please enter more than one step to validate your proof"
    }

    if (z3 === 'sat') {
      return "Your proof is incorrect"
    }

    if (z3 === 'unsat') {
      return "Your proof is correct, well done!"
    }

    return "There are errors in your proof"
  }

  render() {
    const { z3 } = this.props

    return (
      <div className={cx(styles.feedback, { [styles.error]: z3 !== 'unsat' })}>
        { this.getFeedbackText() }
      </div>
    )
  }
}

export default Feedback
