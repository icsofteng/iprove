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

const Controls = () =>
  <div className={styles.controlList}>
    <ControlBlock type="binary" label="Binary Rule" symbol="?" exprLeft exprRight />
    <ControlBlock type="unary" label="Unary Rule" symbol="?" exprRight />
    <ControlBlock type="literal" label="Literal" symbol="x" />
    <ControlBlock type="true" label="True" symbol="⊤" />
    <ControlBlock type="false" label="False" symbol="⊥" />
  </div>

export default Controls