import React, { Component } from 'react'
import cx from 'classnames'
import RuleControls from 'components/RuleControls'
import styles from './styles.scss'

export default class Rule extends Component {
  constructor(props) {
    super(props)

    this.state = {
      value: this.props.value || '',
    }
  }

  onKeyDown = (event) => {
    const charCode = event.charCode || event.keyCode

    const {
      createRule,
      deleteRule,
      moveSelectionUp,
      moveSelectionDown,
      index,
    } = this.props

    /* eslint-disable default-case */
    switch (charCode) {
      case 13:
        // Enter key pressed
        event.preventDefault()
        createRule(index)
        break;
      case 38:
        // Up arrow
        event.preventDefault()
        moveSelectionUp(index)
        break;
      case 40:
        // Down arrow
        event.preventDefault()
        moveSelectionDown(index)
        break;
      case 8:
        // Backspace
        if (event.target.value === '') {
          event.preventDefault()
          deleteRule(index)
        }
        break;
    }
    /* eslint-enable default-case */
  }

  onChange = (event) => {
    const { index, onChange } = this.props
    this.setState({ value: event.target.value })
    onChange(index, event.target.value)
  }

  onRemoveClick = (event) => {
    const { deleteRule, index } = this.props
    event.preventDefault()
    deleteRule(index)
  }

  componentWillReceiveProps = (newProps) => {
    if (newProps.value !== this.props.value) {
      this.setState({ value: newProps.value })
    }
  }

  appendText = (text) => {
    this.setState(oldState => ({ value: oldState.value + text }))
  }

  render() {
    const { value } = this.state
    const { innerRef } = this.props

    return (
      <li>
        <input
          type="text"
          value={value}
          onKeyDown={this.onKeyDown}
          onChange={this.onChange}
          ref={innerRef}
          className={cx(styles.ruleInput)}
        />
        <RuleControls appendText={this.appendText} />
        <span onClick={this.onRemoveClick}>remove</span>
      </li>
    )
  }
}
