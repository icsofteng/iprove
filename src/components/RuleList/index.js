/* Dependencies */
import React, { Component } from 'react'
import cx from 'classnames'

/* Components */
import Rule from 'components/Rule'

/* Styles */
import styles from './styles.scss'

class RuleList extends Component {

  constructor(props) {
    super(props)

    this.state = {
      rules: [''],
      focusIndex: 0,
    }

    this.inputRefs = []

    this.createRule = this.createRule.bind(this)
    this.deleteRule = this.deleteRule.bind(this)
    this.moveSelectionUp = this.moveSelectionUp.bind(this)
    this.moveSelectionDown = this.moveSelectionDown.bind(this)
    this.onChange = this.onChange.bind(this)
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

  deleteRule(index) {
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

  componentDidUpdate(prevProps, prevState) {
    // console.log('update', prevState, this.state)
    // if (prevState.rules.length !== this.state.rules.length) {
    //   console.log('focus on ', this.state.focusIndex)
    //   this.inputRefs[this.state.focusIndex].focus()
    // }
  }

  onChange(index, value) {
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

export default RuleList
