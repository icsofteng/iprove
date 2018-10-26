import React, { Component } from 'react'
import MathJax from 'react-mathjax'
import { connect } from 'react-redux'

import { UPDATE_RULE, ADD_CONSTANTS, SET_STEP_DEPENDENCY } from '../../../constants'
import DependencyList from '../../Shared/DependencyList'

import { translate_rule as translate_mathjax } from '../../../translator/mathjax'
import { translate_rule as translate_raw } from '../../../translator/raw'

import styles from './styles.scss'

class TextBox extends Component {
  constructor(props) {
    super(props)

    this.state = {
      raw: '',
      edit: true,
    }
    this.ref = null
  }

  componentDidMount() {
    const translation = translate_raw(this.props.ast)

    this.setState({
      raw: translation,
      edit: Object.keys(this.props.ast).length === 0
    })

    if (this.props.focus) {
      this.ref.focus()
    }
  }

  componentDidUpdate(prevProps, prevState) {
    // Changing edit and focus props
    if ((prevProps.focus !== this.props.focus || prevState.edit !== this.state.edit) && this.props.focus) {
      if (this.ref) {
        this.ref.focus()
      } else {
        this.setState({ edit: true })
      }
    }
  }

  parseInput(statement) {
    if (statement !== '') {
      fetch('/parse?input=' + statement).then(r => r.json()).then(response => {
        const { ast, constants } = response
        this.props.updateRule(ast[0], [this.props.index, "ast"])
        this.props.addConstants(constants)
        this.setState({ edit: false })
      })
    }
  }

  keyDown(event) {
    if (event.keyCode === 13 || event.keyCode === 9) {
      event.preventDefault()

      if (event.shiftKey) {
        this.props.onIncInput(-1)
      } else {
        this.props.onIncInput(1)
      }

      this.parseInput(event.target.value)
    }
  }

  render() {
    const { ast, index, step: { dependencies } } = this.props

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
              onChange={(event) => this.setState({ raw: event.target.value })}
              onKeyDown={(event) => this.keyDown(event)}
              onFocus={() => this.props.onFocus()}
              onBlur={(event) => this.parseInput(event.target.value)}
              ref={(ref) => this.ref = ref}
            />
          </div>
          :
          <div className={styles.mathjax} onClick={() => {this.props.onFocus(); this.setState({ edit: true })}}>
            <MathJax.Provider>
              <MathJax.Node formula={translate_mathjax(ast)} />
            </MathJax.Provider>
          </div>
        }
        <div className={styles.dependencies}>
          <div className={styles.using}>using</div>
          <DependencyList index={index} dependencies={dependencies} path={[index, "dependencies"]} />
        </div>
      </div>
    )
  }
}

const mapDispatchToProps = dispatch => ({
  updateRule: (object, path) => dispatch({ type: UPDATE_RULE, payload: object, path }),
  addConstants: (values) => dispatch({ type: ADD_CONSTANTS, payload: values }),
  setDependency: (list, path) => dispatch({ type: SET_STEP_DEPENDENCY, payload: list, path })
})

export default connect(null, mapDispatchToProps)(TextBox)
