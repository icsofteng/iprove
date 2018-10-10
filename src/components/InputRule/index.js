import React, { Component } from 'react'

class InputRule extends Component {

  constructor(props) {
    super(props)

    this.state = {
      value: '',
    }

    this.onKeyPress = this.onKeyPress.bind(this)
    this.onChange = this.onChange.bind(this)
  }

  onKeyPress(event) {
    if (event.charCode === 13) {
      // Enter key pressed
      const { addRule } = this.props
      event.preventDefault()
      addRule(event.target.value)
      this.setState({ value: '' })
    }
  }

  onChange(event) {
    this.setState({ value: event.target.value })
  }

  render() {
    const { value } = this.state

    return (
      <li>
        <input
          type="text"
          value={value}
          onKeyPress={this.onKeyPress}
          onChange={this.onChange}
        />
      </li>
    )
  }
}

export default InputRule
