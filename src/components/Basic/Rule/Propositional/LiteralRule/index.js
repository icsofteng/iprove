import React, { Component } from 'react'
import styles from '../../styles.scss'

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
          const upper = event.target.value.toUpperCase()
          this.props.addIdentifiers({ value: upper, varType: "Bool" })
          this.props.updateValue([...this.props.path, "value"], upper)
          this.props.updateValue([...this.props.path, "varType"], "Bool")
        }}
        className={styles.ruleInput}
        ref={(ref) => this.ref = ref}
      />
    )
  }
}

export default LiteralRule
