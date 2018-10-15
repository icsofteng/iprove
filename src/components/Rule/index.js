import React, { Component } from 'react'
import { connect } from 'react-redux'
import cx from 'classnames'
import styles from './styles.scss'
import { REMOVE_RULE, NEW_RULE, CHANGE_FOCUS, UPDATE_RULE } from '../../constants'

class Rule extends Component {
  constructor(props) {
    super(props)
    this.input = null
  }

  componentDidUpdate() {
    if (this.isSelected()) {
      this.input.focus()
    }
  }

  onKeyDown = (event) => {
    const charCode = event.charCode || event.keyCode
    const ENTER = 13;
    const UP = 38;
    const DOWN = 40;
    const BACKSPACE = 8;
    switch (charCode) {
      case ENTER: this.props.createRule(); break;
      case UP: this.props.moveSelectionUp(this.props.index); break;
      case DOWN: this.props.moveSelectionDown(this.props.index); break;
      case BACKSPACE:
        if (event.target.value === '') {
          this.props.deleteRule(this.props.index)
        }
        break
      default: break
    }
  }

  isSelected() {
    return this.props.focus === this.props.index
  }

  render() {
    return (
      <li className={cx({[styles.rule_focus]: this.isSelected() })}>
        <input
          type="text"
          value={this.props.value}
          onKeyDown={this.onKeyDown}
          onFocus={()=>this.props.onFocus(this.props.index)}
          onChange={(event)=>this.props.updateRule(event.target.value)}
          className={cx(styles.ruleInput)}
          ref={(ref)=>this.input=ref}
        />
        <span onClick={()=>this.props.deleteRule(this.props.index)}>remove</span>
      </li>
    )
  }
}

const mapStateToProps = state => {
  return { focus: state.rules.focus }
}

const mapDispatchToProps = dispatch => {
  return {
    moveSelectionUp: (currentIndex) => dispatch({ type: CHANGE_FOCUS, payload: currentIndex - 1 }),
    moveSelectionDown: (currentIndex) => dispatch({ type: CHANGE_FOCUS, payload: currentIndex + 1 }),
    createRule: () => dispatch({ type: NEW_RULE }),
    deleteRule: (index) => dispatch({ type: REMOVE_RULE, payload: index }),
    updateRule: (text) => dispatch({ type: UPDATE_RULE, payload: text }),
    onFocus: (index) => dispatch({ type: CHANGE_FOCUS, payload: index })
  }
}

export default connect(mapStateToProps, mapDispatchToProps)(Rule)