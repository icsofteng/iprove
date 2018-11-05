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
    <ControlBlock type="binary" label="Binary Rule" symbol="?" exprLeft exprRight {...props} />
    <ControlBlock type="unary" label="Unary Rule" symbol="?" exprRight {...props}/>
    <ControlBlock type="literal" label="Literal" symbol="P" {...props}/>
    <ControlBlock type="true" label="True" symbol="⊤" {...props}/>
    <ControlBlock type="false" label="False" symbol="⊥" {...props}/>
    <ControlBlock type="universal_quantifier" label="For all" symbol="∀"  {...props}/>
    <ControlBlock type="existential_quantifier" label="Exists" symbol="∃"  {...props}/>
    <ControlBlock type="relation" label="Relation" symbol="f(x)"  {...props}/>
    <ControlBlock type="variable" label="Variable" symbol="x"  {...props}/>
    <ControlBlock type="constant" label="Constant" symbol="A"  {...props}/>
  </div>

export default Controls
