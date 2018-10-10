import React, { Component } from 'react'

import Rule from 'components/Rule'
import InputRule from 'components/InputRule'

class RuleList extends Component {

  constructor(props) {
    super(props)

    this.state = {
      rules: [1, 2, 3]
    }

    this.addRule = this.addRule.bind(this)
  }

  addRule(rule) {
    this.setState(oldState => (
      this.setState({
        rules: oldState.rules.concat(rule)
      })
    ))
  }

  render() {
    const { rules } = this.state

    return (
      <ul>
        { rules.map(rule => (
          <Rule rule={rule} />
        )) }
        <InputRule addRule={this.addRule} />
      </ul>
    )
  }
}

export default RuleList
