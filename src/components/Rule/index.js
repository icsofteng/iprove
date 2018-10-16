import React from 'react'
import { connect } from 'react-redux'
import styles from './styles.scss'
import { UPDATE_RULE, UPDATE_RULE_LHS, UPDATE_RULE_RHS, REMOVE_RULE, CHANGE_SYMBOL} from '../../constants'
import RulePlaceholder from '../RulePlaceholder'

const SymbolChooser = ({changeSymbol, current, index, symbols}) =>
  <select className={styles.ruleSymbol} value={current} onChange={(event)=>changeSymbol(index, event.target.value)}> 
    <option>...</option>
    {
      Object.keys(symbols).map((key, i) =>
        <option value={key} key={i}>{symbols[key]}</option>
      )
    } 
  </select>

const BinaryRule = (props) =>
  <React.Fragment>
    {/* <input type="text" value={props.lhs} onChange={(event)=>props.updateLhs(props.index, event.target.value)} className={styles.ruleInput} /> */}
    <RulePlaceholder/>
    <SymbolChooser changeSymbol={props.changeSymbol} current={props.symbol} index={props.index} symbols={binSymbols} />
    <input type="text" value={props.rhs} onChange={(event)=>props.updateRhs(props.index, event.target.value)} className={styles.ruleInput} />
  </React.Fragment>

const UnaryRule = (props) =>
  <React.Fragment>
    <SymbolChooser changeSymbol={props.changeSymbol} current={props.symbol} index={props.index} symbols={unRules} />
    <input type="text" value={props.value} onChange={(event)=>props.updateValue(props.index, event.target.value)} className={styles.ruleInput} />
  </React.Fragment>

const LiteralRule = (props) =>
  <input type="text" value={props.value} onChange={(event)=>props.updateValue(props.index, event.target.value)} className={styles.ruleInput} />

const TrueRule = () =>
  <input type="text" value="⊤" disabled className={styles.ruleInput} />

const FalseRule = () =>
  <input type="text" value="⊥" disabled className={styles.ruleInput} />

const binSymbols = {
  and: '∧',
  or: '∨',
  implies: '⇒',
  iff: '⇔'
}

const unRules = {
  not: '¬'
}

const components = {
  binary: BinaryRule,
  unary: UnaryRule,
  literal: LiteralRule,
  true: TrueRule,
  false: FalseRule
}

const Rule = (props) => {
  const RuleType = components[props.type]
  return (
    <div className={styles.rule}>
      <RuleType {...props} />
      <span className={styles.remove} onClick={()=>props.deleteRule(props.index)}>X</span>
    </div>
  )
}

const mapDispatchToProps = dispatch => {
  return {
    updateLhs: (index, value) => dispatch({ type: UPDATE_RULE_LHS, payload: value, index }),
    updateRhs: (index, value) => dispatch({ type: UPDATE_RULE_RHS, payload: value, index }),
    updateValue: (index, value) => dispatch({ type: UPDATE_RULE, payload: value, index }),
    changeSymbol: (index, value) => dispatch({ type: CHANGE_SYMBOL, payload: value, index }),
    deleteRule: (index) => dispatch({ type: REMOVE_RULE, payload: index }),
  }
}

export default connect(null, mapDispatchToProps)(Rule)