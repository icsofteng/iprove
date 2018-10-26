import React, { Component } from 'react'
import { connect } from 'react-redux'
import cx from 'classnames'
import { ADD_STEP_DEPENDENCY } from '../../../constants'
import Dependency from '../Dependency'
import styles from './styles.scss'

class DependencyList extends Component {
  onClick(event) {
    event.preventDefault()
    this.props.addDependency(this.props.path)
  }

  render() {
    const { dependencies, path } = this.props

    return (
      <div className={styles.stepDependencies}>
        { dependencies && dependencies.map((dependency, index) => (
          <Dependency
            value={dependency}
            key={`dependency-${index}-${dependencies.length}`}
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

export default connect(null, mapDispatchToProps)(DependencyList)
