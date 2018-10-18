import React, { Component } from 'react'
import { connect } from 'react-redux'
import { REMOVE_RULE, UPDATE_RULE, ADD_CONSTANT} from '../../constants'
import BinaryRule from './BinaryRule'
import UnaryRule from './UnaryRule'
import LiteralRule from './LiteralRule'
import TrueRule from './TrueRule'
import FalseRule from './FalseRule'
import MathJax from 'react-mathjax'
import { translate_rule } from '../../translator/mathjax'
import styles from './styles.scss'

const components = {
  binary: BinaryRule,
  unary: UnaryRule,
  literal: LiteralRule,
  true: TrueRule,
  false: FalseRule
}

class Rule extends Component {
  constructor(props) {
    super(props)
    this.state = { mathjax: false }
  }
  render() {
    const RuleType = components[this.props.type]
    return this.state.mathjax ?
      <MathJax.Provider>
        <MathJax.Node formula={translate_rule(this.props)} />
      </MathJax.Provider>
      :
      <div className={styles.rule}>
        <RuleType {...this.props} />
        <span
          className={styles.remove}
          onClick={() => this.props.deleteRule(this.props.path)}
        >
          X
        </span>
      </div>
  }
}

const mapDispatchToProps = dispatch => ({
  addConstant: (value) => dispatch({ type: ADD_CONSTANT, payload: value }),
  updateValue: (path, value) => dispatch({ type: UPDATE_RULE, payload: value, path }),
  deleteRule: (path) => dispatch({ type: REMOVE_RULE, path }),
})

export default connect(null, mapDispatchToProps)(Rule)
