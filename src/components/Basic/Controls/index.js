import React from 'react'
import cx from 'classnames'
import styles from './styles.scss'

const ControlBlock = ({ type, label, symbol, exprLeft=false, exprRight }) =>
  <div data-type={type} className={cx('drag-drop', styles.controlBlock)}>
    <div className={styles.label}>{label}</div>
    <div className={styles.template}>
      { exprLeft && <div className={styles.exprPlaceholder}></div> }
      <div className={styles.symbolPlaceholder}>{symbol}</div>
      { exprRight && <div className={styles.exprPlaceholder}></div> }
    </div>
  </div>

const Controls = (props) =>
  <div className={styles.controlList}>
<<<<<<< 9dc2ecdccf81e2db433464e2446753e44fc4e668
    <ControlBlock type="binary" label="Binary Rule" symbol="?" exprLeft exprRight {...props} />
    <ControlBlock type="unary" label="Unary Rule" symbol="?" exprRight {...props}/>
    <ControlBlock type="literal" label="Literal" symbol="P" {...props}/>
    <ControlBlock type="true" label="True" symbol="⊤" {...props}/>
    <ControlBlock type="false" label="False" symbol="⊥" {...props}/>
=======
    <ControlBlock type="binary" label="Binary Rule" symbol="?" exprLeft exprRight />
    <ControlBlock type="unary" label="Unary Rule" symbol="?" exprRight />
    <ControlBlock type="literal" label="Literal" symbol="x" />
    <ControlBlock type="true" label="True" symbol="⊤" />
    <ControlBlock type="false" label="False" symbol="⊥" />
    <ControlBlock type="quantifier" label="For all" symbol="∀" />
    <ControlBlock type="quantifier" label="Exists" symbol="∃" />
>>>>>>> add basic mode for first order logic
  </div>

export default Controls
