import React, { Component } from 'react'
import MathJax from 'react-mathjax'
import { translate_rule as translate_mathjax } from '../../../translator/mathjax'
import { translate_rule as translate_raw } from '../../../translator/raw'
import styles from './styles.scss'
import { connect } from 'react-redux'
import { UPDATE_RULE, ADD_CONSTANTS, SET_STEP_DEPENDENCY } from '../../../constants'

class TextBox extends Component {
  constructor(props) {
    super(props)
    this.state = {
      raw: '',
      edit: true,
      dependencies: (props.dependencies && props.dependencies.join(", ")) || '',
      focusDependencies: false
    }
    this.ref = null
  }

  componentDidMount() {
    const translation = translate_raw(this.props.ast)
    this.setState({
      raw: translation,
      edit: Object.keys(this.props.ast).length === 0
    })
    if (this.props.focus && !this.state.focusDependencies) {
      this.ref.focus()
    }
  }

  componentDidUpdate(prevProps, prevState) {
    // Changing dependencies props
    if (this.props.dependencies) {
      const diffDependencies = this.props.dependencies.filter((el, i) => prevProps.dependencies[i] !== el)
      if (diffDependencies.length > 0 || prevProps.dependencies.length !== this.props.dependencies.length) {
        this.setState({ dependencies: this.props.dependencies.join(", ") })
      }
    }

    // Changing edit and focus props
    if (prevProps.focus !== this.props.focus || prevState.edit !== this.state.edit) {
      if (this.props.focus && !this.state.focusDependencies) {
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
        const { ast, constants } = response
        this.props.updateRule(ast[0], [this.props.type, this.props.index, "ast"])
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
      }
      else {
        this.props.onIncInput(1)
      }
      this.parseInput(event.target.value)
    }
  }

  render() {
    const { ast, index, offset } = this.props
    return (
      <div className={styles.step}>
        <div className={styles.lineNumber}>{offset + index + 1}</div>
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
              <MathJax.Node formula={translate_mathjax(ast)} />
            </MathJax.Provider>
          </div>
        }
        {
          this.props.showDependencies &&
            <div className={styles.dependencies}>
              <div className={styles.using}>using</div>
              <input
                type="text"
                className={styles.dependencyTextbox}
                value={this.state.dependencies || ''}
                onChange={(event)=>this.setState({dependencies: event.target.value})}
                onFocus={()=>this.setState({ focusDependencies: true })}
                onBlur={(event)=>{
                  this.setState({ focusDependencies: false })
                  this.props.setDependency(event.target.value.replace(/\s/g, "").split(","), [this.props.type, index, "dependencies"])
                }}
              />
            </div>
        }
      </div>
    )
  }
}

const mapDispatchToProps = dispatch => ({
  updateRule: (object, path) => dispatch({ type: UPDATE_RULE, payload: object, path }),
  addConstants: (values) => dispatch({ type: ADD_CONSTANTS, payload: values, path: [] }),
  setDependency: (list, path) => dispatch({ type: SET_STEP_DEPENDENCY, payload: list, path }),
})

export default connect(state => ({ givens: state.givens }), mapDispatchToProps)(TextBox)