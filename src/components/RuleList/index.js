/* Dependencies */
import React, { Component } from 'react'
import cx from 'classnames'

/* Components */
import Rule from 'components/Rule'

/* Styles */
// import styles from 'styles.scss'

class RuleList extends Component {

  constructor(props) {
    super(props)

    this.state = {
      rules: [1, 2, 3],
    }

    this.inputRefs = []

    this.createRule = this.createRule.bind(this)
    this.moveSelectionUp = this.moveSelectionUp.bind(this)
    this.moveSelectionDown = this.moveSelectionDown.bind(this)
  }

  moveSelectionUp(index) {
    if (index > 0) {
      this.inputRefs[index - 1].focus()
    }
  }

  moveSelectionDown(index) {
    if (index < this.inputRefs.length - 1) {
      this.inputRefs[index + 1].focus()
    }
  }

  createRule(index) {
    this.setState(oldState => {
      oldState.rules.splice(index, 0, '')

      this.setState({
        rules: oldState.rules,
      })
    })

    if (this.inputRefs.length - 1 > index) {
      this.inputRefs[index].focus()
    }
  }

  render() {
    const { rules } = this.state

    return (
      <ul>
        { rules.map((rule, index) => (
          <Rule
            value={rule}
            index={index}
            innerRef={(ref) => this.inputRefs[index] = ref}
            createRule={this.createRule}
            moveSelectionUp={this.moveSelectionUp}
            moveSelectionDown={this.moveSelectionDown}
          />
        )) }
        <Rule
          index={this.state.rules.length}
          innerRef={(ref) => this.inputRefs[this.state.rules.length] = ref}
          createRule={this.createRule}
          moveSelectionUp={this.moveSelectionUp}
          moveSelectionDown={this.moveSelectionDown}
        />
      </ul>
    )
  }
}

export default RuleList
