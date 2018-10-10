import React, { Component } from 'react'

class Rule extends Component {

  constructor(props) {
    super(props)

    this.state = {
      value: this.props.value || '',
    }

    this.onKeyDown = this.onKeyDown.bind(this)
    this.onChange = this.onChange.bind(this)
  }

  onKeyDown(event) {
    const charCode = event.charCode ? event.charCode : event.keyCode

    const {
      createRule,
      moveSelectionUp,
      moveSelectionDown,
      index,
    } = this.props

    /* eslint-disable default-case */
    switch (charCode) {
      case 13:
        // Enter key pressed
        event.preventDefault()
        createRule(index + 1)
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
    }
    /* eslint-enable default-case */
  }

  onChange(event) {
    this.setState({ value: event.target.value })
  }

  componentWillReceiveProps(newProps) {
    if (newProps.value !== this.props.value) {
      this.setState({ value: newProps.value })
    }
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
        />
      </li>
    )
  }
}

export default Rule
