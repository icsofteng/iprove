import React, { Component } from 'react'
import styles from '../styles.scss'

class LiteralRule extends Component {
  componentDidMount() {
    if (this.ref) {
      this.ref.focus()
    }
  }
  
  render() {
    return (
      <input
        type="text"
        value={this.props.value}
        onChange={(event) => {
          this.props.addConstants(event.target.value)
          this.props.updateValue([...this.props.path, "value"], event.target.value)
        }}
        className={styles.ruleInput}
        ref={(ref) => this.ref = ref}
      />
    )
  }
}
  
export default LiteralRule
