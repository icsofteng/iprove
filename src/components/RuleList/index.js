/* Dependencies */
import React, { Component } from 'react'
import cx from 'classnames'
import Rule from 'components/Rule'
import RuleControls from 'components/RuleControls'
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
      this.onFocus(index - 1)
    }
  }

  moveSelectionDown = (index) => {
    if (index < this.inputRefs.length - 1) {
      this.onFocus(index + 1)
    }
  }

  createRule = () => {
    this.setState(state => ({
      rules: [...state.rules, '']
    }), () =>
      this.onFocus(this.state.rules.length - 1)
    )
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
    }
    else if (index < this.state.rules.length) {
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

  onFocus = (index) => {
    this.setState({ focusIndex: index })
    this.inputRefs[index].focus()
  }

  onSelectRule = (symbol) => {
    this.setState(state => {
      state.rules[state.focusIndex] += symbol
      return state
    })
    this.inputRefs[this.state.focusIndex].focus()
  }

  render() {
    const { rules } = this.state

    return (
      <React.Fragment>
        <RuleControls onSelectRule={this.onSelectRule} />
        <ul className={cx(styles.ruleList)}>
        { rules.map((rule, index) => (
          <Rule
            key={"rule"+index}
            value={rule}
            index={index}
            isFocus={this.state.focusIndex === index}
            innerRef={(ref) => this.inputRefs[index] = ref}
            onChange={this.onChange}
            createRule={this.createRule}
            deleteRule={this.deleteRule}
            moveSelectionUp={this.moveSelectionUp}
            moveSelectionDown={this.moveSelectionDown}
            onFocus={this.onFocus}
          />
        )) }
      </ul>
      </React.Fragment>
    )
  }
}