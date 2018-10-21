import React, { Component } from 'react'
import { connect } from 'react-redux'
import cx from 'classnames'

import { ADD_STEP_DEPENDENCY } from '../../constants'
import StepDependency from './StepDependency'

import styles from './styles.scss'

class StepDependencies extends Component {
  onClick(event) {
    event.preventDefault()
    this.props.addDependency(this.props.path)
  }

  render() {
    const { rule: { dependencies }, path } = this.props

    return (
      <div className={styles.stepDependencies}>
        { dependencies && dependencies.map((dependency, index) => (
          <StepDependency
            dependency={dependency}
            key={"dependency" + index}
            index={index}
            path={path}
          />
        )) }

        <span className={cx(styles.addDependency)} onClick={e => this.onClick(e)}>
          +
        </span>
      </div>
    )
  }
}

const mapDispatchToProps = dispatch => ({
  addDependency: (path) => dispatch({ type: ADD_STEP_DEPENDENCY, path }),
})

export default connect(null, mapDispatchToProps)(StepDependencies)
