import React, { Component } from 'react'
import cx from 'classnames'
import DependencyBox from '../DependencyBox'
import { connect } from 'react-redux'
import styles from './styles.scss'
import LineNumber from './LineNumber'
import LatexView from './LatexView'
import EditView from './EditView'
import { SET_SELECTED, UPDATE_DEP_KEY_DOWN, UPDATE_DEP_NOTHING, ENABLE_EDIT, PARSE_NOTHING, PARSE_KEY_DOWN } from '../../../constants'

class TextBox extends Component {
  constructor(props) {
    super(props)
    this.ref = null
    this.refDep = null
  }

  componentDidMount() {
    this.focusElements()
  }

  componentDidUpdate(prevProps) {
    if (prevProps.selectedTextBox[0] !== this.props.selectedTextBox[0] ||
        prevProps.selectedTextBox[1] !== this.props.selectedTextBox[1] ||
        prevProps.selectedTextBox[2] !== this.props.selectedTextBox[2]) {
      this.focusElements()
    }
  }

  focusElements() {
    if (this.props.selectedTextBox[0] === this.props.type && this.props.selectedTextBox[1] === this.props.index) {
      if (this.ref && !this.props.selectedTextBox[2]) {
        this.ref.focus()
      }
      else if (this.refDep && this.props.selectedTextBox[2]) {
        this.refDep.focus()
      }
    }
  }

  parse = (event, callback) => {
    const { value } = event.target
    if (value !== '') {
      const { identifiers, relations, functions } = this.props
      const url = `/parse?input=${encodeURIComponent(value)}&identifiers=${JSON.stringify(identifiers)}&relations=${JSON.stringify(relations)}&functions=${JSON.stringify(functions)}`
      fetch(url).then(r => r.json()).then(response => callback(response))
    }
  }

  parseAndKeyDown = (event) => {
    if (event.keyCode === 9 || event.keyCode === 13) {
      event.preventDefault()
      event.persist()
      this.parse(event, (response) => this.props.parseAndKeyDown(response, event.keyCode))
    }
  }

  updateDependenciesAndKeyDown = (event) => {
    if (event.keyCode === 9 || event.keyCode === 13) {
      event.preventDefault()
      event.persist()
      this.props.updateDependenciesAndKeyDown(event.target.value)
    }
  }
  
  onFocus = (isDependency) =>
    this.props.setSelected([this.props.type, this.props.index, isDependency])

  hasCorrectClass() {
    const { step: { ast }, type, z3 } = this.props
    return (type !== 'givens' && z3 === 'unsat') || ast.type === 'assume' || ast.type === 'arbitrary' || ast.type === 'exit' || ast.type === 'case'
  }

  hasErrorClass() {
    const { step: { ast }, type, z3, errors = false } = this.props
    return Object.keys(ast).length > 1 && (type !== 'givens' || (type === 'givens' && errors)) && z3 !== 'unsat' && !this.hasCorrectClass()
  }

  render() {
    return (
      <div className={cx(styles.step, { [styles.correct]: this.hasCorrectClass(), [styles.error]: this.hasErrorClass() })}>
        <LineNumber {...this.props} />
        {
          this.props.step.edit ?
          <EditView
            ast={this.props.step.ast}
            onKeyDown={this.parseAndKeyDown}
            onFocus={() => this.onFocus(false)}
            onBlur={(event) => this.parse(event, (response) => this.props.parseAndNothing(response))}
            onRef={(ref) => this.ref = ref}
          /> :
          <LatexView
            onFocus={() => this.props.enableEditMode([this.props.type, this.props.index])}
            ast={this.props.step.ast}
          />
        }
        <DependencyBox
          show={this.props.dependencies}
          ast={this.props.step.ast}
          onFocus={() => this.onFocus(true)}
          onBlur={(event) => this.props.updateDependenciesAndNothing(event.target.value)}
          onKeyDown={this.updateDependenciesAndKeyDown}
          onRef={(ref) => this.refDep = ref}
          value={this.props.step.dependencies}
        />
      </div>
    )
  }
}

const mapDispatchToProps = dispatch => ({
  setSelected: (selected) => dispatch({ type: SET_SELECTED, payload: selected }),
  updateDependenciesAndKeyDown: (payload) => dispatch({ type: UPDATE_DEP_KEY_DOWN, payload }),
  updateDependenciesAndNothing: (payload) => dispatch({ type: UPDATE_DEP_NOTHING, payload }),
  enableEditMode: (path) => dispatch({ type: ENABLE_EDIT, path }),
  parseAndNothing: (payload) => dispatch({ type: PARSE_NOTHING, payload }),
  parseAndKeyDown: (payload, keyCode) => dispatch({ type: PARSE_KEY_DOWN, payload, keyCode })
})

const mapStateToProps = state => {
  const { givens, identifiers, relations, functions, selectedTextBox } = state.present
  return { givens, identifiers, relations, functions, selectedTextBox }
}

export default connect(mapStateToProps, mapDispatchToProps)(TextBox)