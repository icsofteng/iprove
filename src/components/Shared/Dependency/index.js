import React, { Component } from 'react'
import { connect } from 'react-redux'
import cx from 'classnames'

import {
  REMOVE_STEP_DEPENDENCY,
  UPDATE_STEP_DEPENDENCY,
  ADD_STEP_DEPENDENCY_INDEX,
} from '../../../constants'

import styles from './styles.scss'

class Dependency extends Component {
  constructor(props) {
    super(props)

    this.state = {
      value: this.props.value || ''
    }
  }

  onKeyDown(event) {
    const { path, index, removeDependency, addDependencyAtIndex } = this.props
    const charCode = event.charCode || event.keyCode
    const backspaceCode = 8
    const enterCode = 13

    switch (charCode) {
      case backspaceCode:
        if (event.target.value === '') {
          event.preventDefault()
          removeDependency(path, index)
        }
        break

      case enterCode:
        event.preventDefault()
        addDependencyAtIndex(path, index)
        break

      default: break
    }
  }

  onChange(event) {
    const { path, index, updateDependency } = this.props
    this.setState({ value: event.target.value })
    updateDependency(path, index, event.target.value)
  }

  render() {
    return (
      <input
        type="text"
        className={cx(styles.stepDependency)}
        onKeyDown={(event) => this.onKeyDown(event)}
        onChange={(event) => this.onChange(event)}
        value={this.state.value}
      />
    )
  }
}

const mapDispatchToProps = dispatch => ({
  removeDependency: (path, index) => dispatch({ type: REMOVE_STEP_DEPENDENCY, path, index }),
  updateDependency: (path, index, value) => dispatch({ type: UPDATE_STEP_DEPENDENCY, path, index, value }),
  addDependencyAtIndex: (path, index) => dispatch({ type: ADD_STEP_DEPENDENCY_INDEX, path, index })
})

export default connect(null, mapDispatchToProps)(Dependency)
