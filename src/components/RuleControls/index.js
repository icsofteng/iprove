import React from 'react'
import { connect } from 'react-redux'
import cx from 'classnames'
import styles from './styles.scss'
import { CLICK_SYMBOL } from '../../constants';

const controls = ['∧', '∨', '!', '⇒', '⇐', '⇔', '⊤', '⊥']
const RuleControls = (props) =>
  <ul className={cx(styles.ruleControls)}>
    {
      controls.map((symbol, index) =>
        <li key={"control"+index} className={cx(styles.ruleControl)} onClick={()=>props.clickSymbol(symbol)}>{symbol}</li>
      )
    }
  </ul>

const mapDispatchToProps = dispatch => {
  return {
    clickSymbol: (symbol) => dispatch({ type: CLICK_SYMBOL, payload: symbol })
  };
};

export default connect(null, mapDispatchToProps)(RuleControls)