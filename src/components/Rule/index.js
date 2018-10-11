import React from 'react'
import { connect } from 'react-redux'
import cx from 'classnames'
import styles from './styles.scss'
import { REMOVE_RULE, NEW_RULE, CHANGE_FOCUS, UPDATE_RULE } from '../../constants';

const Rule = (props) => {
  const onKeyDown = (event) => {
    const charCode = event.charCode || event.keyCode
    switch (charCode) {
      case 13: props.createRule(); break;
      case 38: props.moveSelectionUp(props.index); break;
      case 40: props.moveSelectionDown(props.index); break;
      case 8:
        if (event.target.value === '') {
          props.deleteRule(props.index)
        }
        break;
      default: break;
    }
  }

  return (
    <li className={cx({[styles.rule_focus]: props.focus === props.index })}>
      <input
        type="text"
        value={props.value}
        onKeyDown={onKeyDown}
        onFocus={()=>props.onFocus(props.index)}
        onChange={(event)=>props.updateRule(event.target.value)}
        className={cx(styles.ruleInput)}
      />
      <span onClick={()=>props.deleteRule(props.index)}>remove</span>
    </li>
  )
}

const mapStateToProps = state => {
  return { focus: state.rules.focus }
}

const mapDispatchToProps = dispatch => {
  return {
    moveSelectionUp: (currentIndex) => dispatch({ type: CHANGE_FOCUS, payload: currentIndex - 1 }),
    moveSelectionDown: (currentIndex) => dispatch({ type: CHANGE_FOCUS, payload: currentIndex + 1 }),
    createRule: () => dispatch({ type: NEW_RULE }),
    deleteRule: (index) => dispatch({ type: REMOVE_RULE, payload: index }),
    updateRule: (text) => dispatch({ type: UPDATE_RULE, payload: text }),
    onFocus: (index) => dispatch({ type: CHANGE_FOCUS, payload: index })
  };
};

export default connect(mapStateToProps, mapDispatchToProps)(Rule)