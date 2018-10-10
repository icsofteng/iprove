import React, { Component } from 'react'
import cx from 'classnames'

import styles from './styles.scss'

class RuleControls extends Component {
  constructor(props) {
    super(props)

    this.onClick = this.onClick.bind(this)
  }

  onClick(event) {
    event.preventDefault()
    this.props.appendText(event.target.innerHTML)
  }

  render() {
    return (
      <div className={cx(styles.ruleControls)}>
        <a href="#" className={cx(styles.ruleControl)} onClick={this.onClick}>∧</a>
        <a href="#" className={cx(styles.ruleControl)} onClick={this.onClick}>∨</a>
        <a href="#" className={cx(styles.ruleControl)} onClick={this.onClick}>!</a>
        <a href="#" className={cx(styles.ruleControl)} onClick={this.onClick}>⇒</a>
        <a href="#" className={cx(styles.ruleControl)} onClick={this.onClick}>⇐</a>
        <a href="#" className={cx(styles.ruleControl)} onClick={this.onClick}>⇔</a>
        <a href="#" className={cx(styles.ruleControl)} onClick={this.onClick}>⊤</a>
        <a href="#" className={cx(styles.ruleControl)} onClick={this.onClick}>⊥</a>
      </div>
    )
  }
}

export default RuleControls
