import React, { Component } from 'react'
import MathJax from 'react-mathjax'
import { translate_rule as translate_mathjax } from '../../../translator/mathjax'
import { translate_rule as translate_raw } from '../../../translator/raw'
import styles from './styles.scss'
import cx from 'classnames'
import _ from 'underscore'
import { connect } from 'react-redux'
import { UPDATE_RULE, ADD_CONSTANTS, ADD_RELATIONS, SET_STEP_DEPENDENCY, ADD_ATOMS } from '../../../constants'

class TextBox extends Component {
  constructor(props) {
    super(props)
    this.state = {
      raw: (props.ast && translate_raw(props.ast)) || '',
      edit: Object.keys(props.ast).filter(k => props.ast[k]).length === 0,
      dependencies: (props.dependencies && props.dependencies.join(", ")) || '',
      focusDependencies: false
    }
    this.ref = null
    this.refDef = null
  }

  componentDidMount() {
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

    // Change ast
    if (!_.isEqual(prevProps.ast, this.props.ast)) {
      const translation = translate_raw(this.props.ast)
      this.setState({
        raw: translation || '',
        edit: Object.keys(this.props.ast).length === 0
      })
    } 

    // Changing edit and focus props
    if (prevProps.focus !== this.props.focus || this.state.edit) {
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
        const { ast, constants, relations, atoms } = response
        this.props.updateRule(ast[0], [this.props.type, this.props.index, "ast"])
        this.props.addConstants(constants)
        this.props.addAtoms(atoms)
        this.props.addRelations(relations)
        this.setState({ edit: false })
      })
    }
  }

  keyDown(event, parse = false) {
    if (event.keyCode === 9) {
      // TAB key
      event.preventDefault()
      if (event.shiftKey) {
        if (this.state.focusDependencies) {
          this.setState({ focusDependencies: false })
          this.ref.focus()
        }
        else {
          this.props.onIncInput(-1)
        }
      }
      else {
        if (this.state.focusDependencies || this.props.type === 'givens') {
          this.setState({ focusDependencies: false })
          this.props.onIncInput(1)
        }
        else if (this.props.type !== 'goal') {
          this.setState({ focusDependencies: true })
          this.refDef.focus()
        }
      }
      if (parse) {
        this.parseInput(event.target.value)
      }
    }
    else if (event.keyCode === 13) {
      // ENTER key
      event.preventDefault()
      if (this.props.type !== 'goal') {
        this.props.onIncInput(1)
      }
      if (parse) {
        this.parseInput(event.target.value)
      }
    }
  }

  render() {
    const { ast, index, offset, z3, type } = this.props
    return (
      <div className={cx(styles.step, {
        [styles.correct]: type !== 'givens' && z3 === 'unsat',
        [styles.error]: this.state.raw !== '' && type !== 'givens' && z3 !== 'unsat'
      })}>
        { type !== 'goal' && <div className={styles.lineNumber}>{offset + index + 1}</div> }
        {
          this.state.edit ?
          <div className={styles.textboxContainer}>
            <input
              type="text"
              className={styles.textbox}
              value={this.state.raw || ''}
              onChange={(event)=>this.setState({raw: event.target.value})}
              onKeyDown={(event)=>this.keyDown(event, true)}
              onFocus={()=>this.props.onFocus()}
              onBlur={(event)=>{
                this.props.onBlur()
                this.parseInput(event.target.value)
              }}
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
              <div className={styles.using} onClick={()=>this.refDef.focus()}>using</div>
              <input
                type="text"
                className={styles.dependencyTextbox}
                value={this.state.dependencies || ''}
                onChange={(event)=>this.setState({dependencies: event.target.value})}
                onKeyDown={(event)=>this.keyDown(event)}
                onFocus={()=>{ this.props.onFocus(); this.setState({ focusDependencies: true })}}
                onBlur={(event)=>{
                  this.props.onBlur()
                  this.setState({ focusDependencies: false })
                  this.props.setDependency(event.target.value.split(/[\s,]+/), [this.props.type, index, "dependencies"])
                }}
                ref={(ref)=>this.refDef=ref}
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
  addRelations: (values) => dispatch({ type: ADD_RELATIONS, payload: values, path: [] }),
  addAtoms: (values) => dispatch({ type: ADD_ATOMS, payload: values, path: [] }),
  setDependency: (list, path) => dispatch({ type: SET_STEP_DEPENDENCY, payload: list, path }),
})

export default connect(state => ({ givens: state.present.givens }), mapDispatchToProps)(TextBox)