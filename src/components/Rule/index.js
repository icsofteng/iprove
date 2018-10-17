import React from 'react'
import { connect } from 'react-redux'
import styles from './styles.scss'
import { REMOVE_RULE, UPDATE_RULE, ADD_CONSTANT} from '../../constants'
import RulePlaceholder from '../RulePlaceholder'

const SymbolChooser = ({updateValue, current, path, symbols}) =>
  <select className={styles.ruleSymbol} value={current} onChange={(event)=>updateValue(path, event.target.value)}> 
    <option>...</option>
    {
      Object.keys(symbols).map((key, i) =>
        <option value={key} key={i}>{symbols[key]}</option>
      )
    } 
  </select>

const BinaryRule = (props) =>
  <React.Fragment>
    { props.lhs ?
      <Rule
        updateValue={props.updateValue}
        deleteRule={props.deleteRule}
        addConstant={props.addConstant}
        path={[...props.path, "lhs"]}
        {...props.lhs}
      /> :
      <RulePlaceholder
        path={[...props.path, "lhs"]}
      />
    }
    <SymbolChooser
      updateValue={props.updateValue}
      current={props.symbol}
      path={[...props.path, "symbol"]}
      symbols={binSymbols}
    />
    { props.rhs ?
      <Rule
        updateValue={props.updateValue}
        deleteRule={props.deleteRule}
        addConstant={props.addConstant}
        path={[...props.path, "rhs"]}
        {...props.rhs}
      /> :
      <RulePlaceholder
        path={[...props.path, "rhs"]}
      />
    }
  </React.Fragment>

const UnaryRule = (props) =>
  <React.Fragment>
    <SymbolChooser
      changeSymbol={props.changeSymbol}
      current={props.symbol}
      path={props.path}
      symbols={unRules} />
    { props.value ?
      <Rule 
        updateValue={props.updateValue}
        deleteRule={props.deleteRule}
        addConstant={props.addConstant}
        {...props.value}
      /> : 
      <RulePlaceholder
        path={[...props.path, "value"]}
      />
    }
  </React.Fragment>

const LiteralRule = (props) =>
  <input
    type="text"
    value={props.value}
    onChange={(event)=>{
      props.addConstant(event.target.value)
      props.updateValue([...props.path, "value"], event.target.value)
    }}
    className={styles.ruleInput}
  />

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
      <span className={styles.remove} onClick={()=>props.deleteRule(props.path)}>X</span>
    </div>
  )
}

const mapDispatchToProps = dispatch => {
  return {
    addConstant: (value) => dispatch({ type: ADD_CONSTANT, payload: value }),
    updateValue: (path, value) => dispatch({ type: UPDATE_RULE, payload: value, path }),
    deleteRule: (path) => dispatch({ type: REMOVE_RULE, path }),
  }
}

export default connect(null, mapDispatchToProps)(Rule)