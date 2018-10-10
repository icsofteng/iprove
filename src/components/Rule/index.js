import React, { Component } from 'react'

class Rule extends Component {

  render() {
    const { rule } = this.props

    return (
      <li>
        <input type="text" value={rule} />
      </li>
    )
  }
}

export default Rule
