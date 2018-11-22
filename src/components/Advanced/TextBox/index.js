import React, { Component } from 'react'
import Latex from 'react-latex'
import cx from 'classnames'
import _ from 'underscore'
import { connect } from 'react-redux'

import { translate_rule as translate_latex } from '../../../translator/latex'
import { translate_rule as translate_raw } from '../../../translator/raw'
import {
  UPDATE_RULE,
  ADD_CONSTANTS,
  ADD_RELATIONS,
  SET_STEP_DEPENDENCY,
  ADD_ATOMS,
  SET_SCOPE,
  ADD_TYPES,
  OPEN_CASE
} from '../../../constants'

import styles from './styles.scss'

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
    if (this.props.focus && !this.state.focusDependencies && this.ref) {
      this.ref.focus()
    }
  }

  componentDidUpdate(prevProps, prevState) {
    // Changing dependencies props
    if (this.props.dependencies && prevProps.dependencies) {
      const diffDependencies = this.props.dependencies.filter((el, i) => prevProps.dependencies[i] !== el)
      if (diffDependencies.length > 0 || prevProps.dependencies.length !== this.props.dependencies.length) {
        this.setState({ dependencies: this.props.dependencies.join(", ") })
      }
    }

    // Change ast
    if (!_.isEqual(prevProps.ast, this.props.ast)) {
      const translation = translate_raw(this.props.ast)
      //checks if the newly updated line was a newly inserted line and if so, clears the text box
      let isInsert = this.state.raw && !this.props.ast.type
      if (translation || isInsert) {
        this.setState({
          raw: isInsert ? '' : translation,
          edit: Object.keys(this.props.ast).length === 0
        })
      }
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
    return new Promise((resolve, reject) => {
      if (statement !== '') {
        fetch('/parse?input=' + encodeURIComponent(statement)).then(r => r.json()).then(response => {
          const { ast, constants, relations, atoms, types } = response
          this.props.updateRule(ast[0], [this.props.type, this.props.index, "ast"])
          this.props.addConstants(constants)
          this.props.addAtoms(atoms)
          this.props.addRelations(relations)
          this.props.addTypes(types)
          if (ast[0].type === 'assume') {
            this.props.setScope(this.props.scope, this.props.index, true)
          }
          else if (ast[0].type === 'case') {
            this.props.setScope(this.props.scope, this.props.index, true)
          }
          else if (ast[0].type === 'exit') {
            this.props.setScope(this.props.scope.slice(0, -1), this.props.index, false)
          }
          this.setState({ edit: false })
          resolve(ast[0])
        })
      }
      else {
        resolve({})
      }
    })
  }

  keyDown(event, parse) {
    let promise = Promise.resolve({})
    const isShift = event.shiftKey
    if (event.keyCode === 9) {
      // TAB key (go to next input)
      event.preventDefault()
      if (parse) {
        promise = this.parseInput(event.target.value)
      }
      promise.then((new_ast) => {
        if (isShift) {
          if (this.state.focusDependencies) {
            this.setState({ focusDependencies: false })
            this.ref.focus()
          }
          else {
            this.props.onIncInput(-1)
          }
        }
        else {
          if (this.state.focusDependencies || this.props.type === 'givens' || new_ast.type === 'assume' || new_ast.type === 'case' || new_ast.type === 'exit') {
            this.setState({ focusDependencies: false })
            this.props.onIncInput(1)
          }
          else if (this.props.type !== 'goal') {
            this.setState({ focusDependencies: true })
            this.refDef.focus()
          }
        }
      })
    }
    else if (event.keyCode === 13) {
      // ENTER key (new line below this one)
      event.preventDefault()
      if (parse) {
        promise = this.parseInput(event.target.value)
      }
      promise.then((new_ast) => {
        if (this.props.type !== 'goal') {
          this.props.newStepAfter(this.props.index)
        }
        if (new_ast.type === 'case') {
          this.props.setScope(this.props.scope.slice(0, -1), this.props.index + 1, false)
        }
      })
    }
    else if (event.keyCode === 8 && event.target.value === '') {
      event.preventDefault()
      this.props.removeCurrentStep(this.props.index)
    }
  }

  render() {
    const { ast, index, offset, z3, type } = this.props
    const isCorrect = (type !== 'givens' && z3 === 'unsat') || ast.type === 'assume' || ast.type === 'exit' || ast.type === 'case'
    return (
      <div className={cx(styles.step, {
        [styles.correct]: isCorrect,
        [styles.error]: this.state.raw !== '' && type !== 'givens' && z3 !== 'unsat' && !isCorrect
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
          <div className={styles.latex} onClick={()=>{this.props.onFocus(); this.setState({ edit: true })}}>
            <Latex>{"$"+translate_latex(ast)+"$"}</Latex>
          </div>
        }
        {
          (this.props.showDependencies && ast.type !== 'assume' && ast.type !== 'exit' && ast.type !== 'case') &&
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
  addTypes: (values) => dispatch({ type: ADD_TYPES, payload: values, path: [] }),
  addAtoms: (values) => dispatch({ type: ADD_ATOMS, payload: values, path: [] }),
  setDependency: (list, path) => dispatch({ type: SET_STEP_DEPENDENCY, payload: list, path }),
  setScope: (scope, thisIndex, override) => dispatch({ type: SET_SCOPE, payload: scope, path: [], thisIndex, override }),
  openCase: (startScope, lhs, rhs) => dispatch({ type: OPEN_CASE, payload: startScope, path: [], lhs, rhs })
})

export default connect(state => ({ givens: state.present.givens }), mapDispatchToProps)(TextBox)
