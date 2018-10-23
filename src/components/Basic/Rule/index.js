import React from 'react'
import { connect } from 'react-redux'
import { REMOVE_RULE, UPDATE_RULE, ADD_CONSTANTS } from '../../../constants'
import BinaryRule from './BinaryRule'
import UnaryRule from './UnaryRule'
import LiteralRule from './LiteralRule'
import TrueRule from './TrueRule'
import FalseRule from './FalseRule'
import styles from './styles.scss'

const components = {
  binary: BinaryRule,
  unary: UnaryRule,
  literal: LiteralRule,
  true: TrueRule,
  false: FalseRule
}

const Rule = (props) => {
  if (props.type === 'paren') {
    return <Rule {...props} {...props.value} />
  }
  const RuleType = components[props.type]
  return (
    <div className={styles.rule}>
      <RuleType {...props} />
      <span className={styles.remove} onClick={() => props.removeRule(props.path)}>X</span>
    </div>
  )
}

const mapDispatchToProps = dispatch => ({
  addConstants: (value) => dispatch({ type: ADD_CONSTANTS, payload: [value] }),
  updateValue: (path, value) => dispatch({ type: UPDATE_RULE, payload: value, path }),
  removeRule: (path) => dispatch({ type: REMOVE_RULE, path }),
})

export default connect(null, mapDispatchToProps)(Rule)
