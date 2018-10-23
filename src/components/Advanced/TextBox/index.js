import React, { Component } from 'react'
import MathJax from 'react-mathjax'
import { translate_rule as translate_mathjax } from '../../../translator/mathjax'
import { translate_rule as translate_raw } from '../../../translator/raw'
import styles from './styles.scss'
import { connect } from 'react-redux'
import { UPDATE_RULE } from '../../../constants'

class TextBox extends Component {
  constructor() {
    super()
    this.state = { raw: '', edit: true }
    this.ref = null
  }

  componentDidMount() {
    const translation = translate_raw(this.props.rule)
    this.setState({ raw: translation, edit: Object.keys(this.props.rule).length === 0 })
    if (this.props.focus) {
      this.ref.focus()
    }
  }

  componentDidUpdate(prevProps, prevState) {
    if (prevProps.focus !== this.props.focus || prevState.edit !== this.state.edit) {
      if (this.props.focus) {
        if (this.ref) {
          this.ref.focus()
        }
        else {
          this.setState({ edit: true })
        }
      }
    }
  }

  parseInput(statement) {
    if (statement !== '') {
      fetch('/parse?input=' + statement).then(r => r.json()).then(response => {
        this.props.updateRule(response[0], [this.props.index])
        this.setState({ edit: false })
      })
    }
  }

  keyDown(event) {
    if (event.keyCode === 13 || event.keyCode === 9) {
      event.preventDefault()
      if (event.shiftKey) {
        this.props.onIncInput(-1)
      }
      else {
        this.props.onIncInput(1)
      }
      this.parseInput(event.target.value)
    }
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
              value={this.state.raw || ''}
              onChange={(event)=>this.setState({raw: event.target.value})}
              onKeyDown={(event)=>this.keyDown(event)}
              onFocus={()=>this.props.onFocus()}
              onBlur={(event)=>this.parseInput(event.target.value)}
              ref={(ref)=>this.ref=ref}
            />
          </div>
          :
          <div className={styles.mathjax} onClick={()=>{this.props.onFocus(); this.setState({ edit: true })}}>
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