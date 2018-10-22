import React, { Component } from 'react'
import MathJax from 'react-mathjax'
import { translate_rule } from '../../translator/mathjax'
import styles from './styles.scss'
import { connect } from 'react-redux'
import { UPDATE_RULE } from '../../constants'

class TextBox extends Component {
  parseInput(statement) {
    fetch('/parse?input=' + statement).then(r => r.json()).then(response => {
      this.props.updateRule(response[0], [this.props.index])
    })
  }

  render() {
    const { rule, index } = this.props
    return (
      <div className={styles.step}>
        <div className={styles.lineNumber}>{index + 1}</div>
        <div className={styles.textboxContainer}>
          <input type="text" className={styles.textbox} onChange={(event)=>this.parseInput(event.target.value)} />
        </div>
        <div className={styles.mathjax}>
          <MathJax.Provider>
            <MathJax.Node formula={translate_rule(rule)} />
          </MathJax.Provider>
        </div>
      </div>
    )
  }
}

const mapDispatchToProps = dispatch => ({
  updateRule: (object, path) => dispatch({ type: UPDATE_RULE, payload: object, path })
})

export default connect(null, mapDispatchToProps)(TextBox)