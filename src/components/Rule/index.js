import React from 'react'
import { connect } from 'react-redux'
import styles from './styles.scss'
import { UPDATE_RULE, UPDATE_RULE_LHS, UPDATE_RULE_RHS, REMOVE_RULE, CHANGE_SYMBOL} from '../../constants'

export const Rule = (props) =>
  <div className={styles.rule}>
    {
      props.type === 'binary' ?
      <React.Fragment>
        <input
          type="text"
          value={props.lhs}
          onChange={(event)=>props.updateLhs(props.index, event.target.value)}
          className={styles.ruleInput}
        />
        <select className={styles.ruleSymbol} value={props.symbol} onChange={(event)=>props.changeSymbol(props.index, event.target.value)}>
          <option>...</option>
          <option value="and">∧</option>
          <option value="or">∨</option>
          <option value="implies">⇒</option>
          <option value="iff">⇔</option>
        </select>
        <input
          type="text"
          value={props.rhs}
          onChange={(event)=>props.updateRhs(props.index, event.target.value)}
          className={styles.ruleInput}
        />
      </React.Fragment>
      :
      <React.Fragment>
        <select className={styles.ruleSymbol} value={props.symbol} onChange={(event)=>props.changeSymbol(props.index, event.target.value)}>
          <option>...</option>
          <option value="not">¬</option>
        </select>
        <input
          type="text"
          value={props.value}
          onChange={(event)=>props.updateValue(props.index, event.target.value)}
          className={styles.ruleInput}
        />
      </React.Fragment>
    }
    
    <span className={styles.remove} onClick={()=>props.deleteRule(props.index)}>X</span>
  </div>

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