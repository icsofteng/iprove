import React, { Component } from 'react'
import { connect } from 'react-redux'
import styles from './styles.scss'
import { REMOVE_RULE} from '../../constants'

class Rule extends Component {
  render() {
    return (
      <div className={styles.rule}>
        {
          this.props.rule.type === 'binary' ?
          <React.Fragment>
            <input
              type="text"
              value={this.props.rule.lhs}
              onChange={(event)=>this.props.updateLhs(event.target.value)}
              className={styles.ruleInput}
            />
            <select className={styles.ruleSymbol}>
              <option>...</option>
              <option>∧</option>
              <option>∨</option>
              <option>⇒</option>
              <option>⇐</option>
              <option>⇔</option>
            </select>
            <input
              type="text"
              value={this.props.rule.rhs}
              onChange={(event)=>this.props.updateRhs(this.props.index, event.target.value)}
              className={styles.ruleInput}
            />
          </React.Fragment>
          :
          <React.Fragment>
            <select className={styles.ruleSymbol}>
              <option>...</option>
              <option>¬</option>
            </select>
            <input
              type="text"
              value={this.props.rule.value}
              onChange={(event)=>this.props.updateValue(this.props.index, event.target.value)}
              className={styles.ruleInput}
            />
          </React.Fragment>
        }
        
        <span className={styles.remove} onClick={()=>this.props.deleteRule(this.props.index)}>X</span>
      </div>
    )
  }
}

const mapDispatchToProps = dispatch => {
  return {
    updateLhs: () => {},
    updateRhs: () => {},
    updateValue: () => {},
    deleteRule: (index) => dispatch({ type: REMOVE_RULE, payload: index }),
  }
}

export default connect(null, mapDispatchToProps)(Rule)