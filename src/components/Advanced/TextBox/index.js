import React, { Component } from 'react'
import MathJax from 'react-mathjax'
import { translate_rule as translate_mathjax } from '../../../translator/mathjax'
import styles from './styles.scss'
import { connect } from 'react-redux'
import { UPDATE_RULE } from '../../../constants'

class TextBox extends Component {
  constructor() {
    super()
    this.state = { raw: '', edit: true }
  }

  parseInput(statement) {
    fetch('/parse?input=' + statement).then(r => r.json()).then(response => {
      this.props.updateRule(response[0], [this.props.index])
      this.setState({ edit: false })
    })
  }

  render() {
    const { rule, index } = this.props
    return (
      <div className={styles.step}>
        <div className={styles.lineNumber}>{index + 1}</div>
        {
          this.state.edit ?
          <div className={styles.textboxContainer}>
            <input
              type="text"
              className={styles.textbox}
              value={this.state.raw}
              onChange={(event)=>this.setState({raw: event.target.value})}
              onKeyUp={(event)=>{if (event.keyCode === 13) this.parseInput(event.target.value)}}
            />
          </div>
          :
          <div className={styles.mathjax} onClick={()=>this.setState({ edit: true })}>
            <MathJax.Provider>
              <MathJax.Node formula={translate_mathjax(rule)} />
            </MathJax.Provider>
          </div>
        }
      </div>
    )
  }
}

const mapDispatchToProps = dispatch => ({
  updateRule: (object, path) => dispatch({ type: UPDATE_RULE, payload: object, path })
})

export default connect(null, mapDispatchToProps)(TextBox)