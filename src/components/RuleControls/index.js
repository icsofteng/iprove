import React, { Component } from 'react'
import cx from 'classnames'
import styles from './styles.scss'

export default class RuleControls extends Component {
  constructor(props) {
    super(props)
    this.state = {
      controls: ['∧', '∨', '!', '⇒', '⇐', '⇔', '⊤', '⊥']
    }
  }

  onClick = (symbol) => {
    this.props.appendText(symbol)
  }

  render() {
    return (
      <ul className={cx(styles.ruleControls)}>
        {
          this.state.controls.map((symbol, index) =>
            <li key={"control"+index} className={cx(styles.ruleControl)} onClick={()=>this.onClick(symbol)}>{symbol}</li>
          )
        }
      </ul>
    )
  }
}
