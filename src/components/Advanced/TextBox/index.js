import React, { Component } from 'react'
import Latex from 'react-latex'
import cx from 'classnames'
import _ from 'underscore'
import { connect } from 'react-redux'

import { translate_rule as translate_latex } from '../../../translator/latex'
import { translate_rule as translate_raw } from '../../../translator/raw'
import {
  UPDATE_RULE,
  ADD_IDENTIFIERS,
  ADD_RELATIONS,
  SET_STEP_DEPENDENCY,
  SET_SCOPE,
  ADD_TYPES,
  ADD_FUNCTIONS
} from '../../../constants'

import styles from './styles.scss'

class TextBox extends Component {
  constructor(props) {
    super(props)
    this.state = {
      raw: (props.ast && translate_raw(props.ast)) || '',
      edit: Object.keys(props.ast).filter(k => props.ast[k]).length <= 1,
      dependencies: (props.dependencies && props.dependencies.join(", ")) || '',
      focusDependencies: false,
      semanticErrors: false
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
      //if (prevState.dependencies !== this.props.dependencies.join(", ")) {
      if (!_.isEqual(prevProps.dependencies, this.props.dependencies)) {
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
    console.log("PARSING!!!!")
    return new Promise((resolve, reject) => {
      if (statement !== '') {
        fetch('/parse?input=' + encodeURIComponent(statement) +
             '&identifiers='+ JSON.stringify(this.props.identifiers) +
             '&relations='+ JSON.stringify(this.props.relations) +
             '&functions='+ JSON.stringify(this.props.functions)
        ).then(r => r.json()).then(response => {
          const newPath = [this.props.type, this.props.index]
          const { ast, identifiers, relations, types, functions, errors } = response
          this.setState({semanticErrors:errors})
          console.log(identifiers)

          if (ast[0].type === 'exit') {
            this.props.setScope(this.props.scope.slice(0, -1), newPath, true)
          }
          else {
            this.props.addIdentifiers(identifiers)
            this.props.addRelations(relations)
            this.props.addTypes(types)
            this.props.addFunctions(functions)
            this.props.updateRule(ast[0], [...newPath, "ast"])
            if (ast[0].type === 'assume') {
              this.props.setScope([...this.props.scope, this.props.index], newPath, false)
            }
            else if (ast[0].type === 'case') {
              this.props.setScope([...this.props.scope, this.props.index], newPath, false)
            }
            this.setState({ edit: false })
          }
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
        if (this.props.type !== 'goal' && (new_ast === undefined || new_ast.type !== 'case')) {
          this.props.newStepAfter(this.props.index)
        }
        if (new_ast.type === 'case') {
          this.props.setScope(this.props.scope.slice(0, -1), [this.props.type, this.props.index+1], false)
        }
      })
    }
    else if (event.keyCode === 8 && event.target.value === '') {
      event.preventDefault()
      this.props.removeCurrentStep(this.props.index)
    }
  }

  render() {
    const { ast, index, offset, z3, type, parentCase } = this.props

    const isCorrect =
      (type !== 'givens' && type !== 'lemmas' && z3 === 'unsat') ||
      ['assume', 'arbitrary', 'exit', 'case'].includes(ast.type)

    const isError =
      this.state.raw !== '' &&
      (type !== 'givens' || (type === 'givens' && this.state.semanticErrors)) &&
      (type !== 'lemmas' || (type === 'lemmas' && this.state.semanticErrors)) &&
      z3 !== 'unsat' &&
      !isCorrect

    const lineNumber = `${type === 'lemmas' ? 'L' : ''}${offset + index + 1}`

    return (
      <div className={cx(styles.step, {
        [styles.correct]: isCorrect,
        [styles.error]: isError
      })}>
        { type !== 'goal' && (
            <div className={styles.lineNumber}>
              {lineNumber} { parentCase && ast.type === 'assume' && "[Case " + parentCase + "]" }
            </div>
          )
        }
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
          (this.props.showDependencies && ast.type !== 'assume' && ast.type !== 'arbitrary' && ast.type !== 'exit' && ast.type !== 'case') &&
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
  addIdentifiers: (values) => dispatch({ type: ADD_IDENTIFIERS, payload: values, path: [] }),
  addRelations: (values) => dispatch({ type: ADD_RELATIONS, payload: values, path: [] }),
  addTypes: (values) => dispatch({ type: ADD_TYPES, payload: values, path: [] }),
  addFunctions: (values) => dispatch({ type: ADD_FUNCTIONS, payload: values, path: [] }),
  setDependency: (list, path) => dispatch({ type: SET_STEP_DEPENDENCY, payload: list, path }),
  setScope: (scope, path, removeLine) => dispatch({ type: SET_SCOPE, payload: scope, path, removeLine })
})

const mapStateToProps = state => {
  const { givens, identifiers, relations, functions } = state.present
  return { givens, identifiers, relations, functions }
}

export default connect(mapStateToProps, mapDispatchToProps)(TextBox)
