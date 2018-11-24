import React from 'react'
import { connect } from 'react-redux'

import { REMOVE_RULE, UPDATE_RULE, ADD_IDENTIFIERS, NEW_RULE } from '../../../constants'

/* Propositional */
import BinaryRule from './Propositional/BinaryRule'
import UnaryRule from './Propositional/UnaryRule'
import LiteralRule from './Propositional/LiteralRule'
import TrueRule from './Propositional/TrueRule'
import FalseRule from './Propositional/FalseRule'

/* First Order */
import Quantifier from './FirstOrder/Quantifier'
import Variable from './FirstOrder/Variable'
import Relation from './FirstOrder/Relation'
import Constant from './FirstOrder/Constant'

import styles from './styles.scss'

const components = {
  binary: BinaryRule,
  unary: UnaryRule,
  literal: LiteralRule,
  true: TrueRule,
  false: FalseRule,
  universal_quantifier: Quantifier,
  existential_quantifier: Quantifier,
  variable: Variable,
  constant: Constant,
  relation: Relation,
}

const Rule = (props) => {
  const removeRuleOrStep = () => {
    let pathWithoutAst = props.path
    if (pathWithoutAst[pathWithoutAst.length - 1] === 'ast') {
      pathWithoutAst.splice(-1, 1)
    }
    props.removeRule(pathWithoutAst)
  }

  if (!props.type) {
    return null
  }

  if (props.type === 'paren') {
    return <Rule {...props} {...props.value} />
  }

  const RuleType = components[props.type]

  if (!RuleType) {
    return null
  }

  return (
    <div className={styles.rule}>
      <RuleType {...props} />
      <span className={styles.remove} onClick={removeRuleOrStep}>X</span>
    </div>
  )
}

const mapDispatchToProps = dispatch => ({
  addIdentifiers: (value) => dispatch({ type: ADD_IDENTIFIERS, payload: [value], path: [] }),
  updateValue: (path, value) => dispatch({ type: UPDATE_RULE, payload: value, path }),
  removeRule: (path) => dispatch({ type: REMOVE_RULE, path }),
  dropLiteral: (path) => dispatch({ type: NEW_RULE, payload: 'literal', path })
})

export default connect(null, mapDispatchToProps)(Rule)
