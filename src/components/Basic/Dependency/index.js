import React, { Component } from 'react'
import { connect } from 'react-redux'
import cx from 'classnames'
import { REMOVE_STEP_DEPENDENCY, UPDATE_STEP_DEPENDENCY } from '../../../constants'
import styles from './styles.scss'

class Dependency extends Component {
  constructor(props) {
    super(props)

    this.state = {
      value: this.props.dependency || ''
    }
  }

  onKeyDown(event) {
    const { path, index, removeDependency } = this.props
    const charCode = event.charCode || event.keyCode

    if (charCode === 8 && event.target.value === '') {
      event.preventDefault()
      removeDependency(path, index)
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
})

export default connect(null, mapDispatchToProps)(Dependency)
