/* Dependencies */
import React, { Component } from 'react'
import cx from 'classnames'
import Rule from 'components/Rule'
import styles from './styles.scss'

export default class RuleList extends Component {
  constructor(props) {
    super(props)

    this.state = {
      rules: [''],
      focusIndex: 0,
    }

    this.inputRefs = []
  }

  moveSelectionUp = (index) => {
    if (index > 0) {
      this.inputRefs[index - 1].focus()
    }
  }

  moveSelectionDown = (index) => {
    if (index < this.inputRefs.length - 1) {
      this.inputRefs[index + 1].focus()
    }
  }

  createRule = (index) => {
    this.setState(oldState => {
      oldState.rules.splice(index + 1, 0, '')

      this.setState({
        rules: oldState.rules,
        focusIndex: index + 1,
      })
    })

    if (this.inputRefs.length - 1 > index) {
      this.inputRefs[index + 1].focus()
    }
  }

  deleteRule = (index) => {
    if (index === 0 && this.state.rules.length === 1) {
      return
    }

    this.setState(oldState => {
      oldState.rules.splice(index, 1)

      this.setState({
        rules: oldState.rules,
        focusIndex: index,
      })
    })

    if (index > 0) {
      this.inputRefs[index - 1].focus()
    } else if (index < this.state.rules.length) {
      this.inputRefs[index].focus()
    }
  }

  onChange = (index, value) => {
    this.setState(oldState => {
      const rules = oldState.rules
      rules[index] = value

      this.setState({ rules })
    })
  }

  render() {
    const { rules } = this.state

    return (
      <ul className={cx(styles.ruleList)}>
        { rules.map((rule, index) => (
          <Rule
            key={"rule"+index}
            value={rule}
            index={index}
            innerRef={(ref) => this.inputRefs[index] = ref}
            onChange={this.onChange}
            createRule={this.createRule}
            deleteRule={this.deleteRule}
            moveSelectionUp={this.moveSelectionUp}
            moveSelectionDown={this.moveSelectionDown}
          />
        )) }
      </ul>
    )
  }
}