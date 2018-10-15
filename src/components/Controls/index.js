import React from 'react'
import { connect } from 'react-redux'
import styles from './styles.scss'
import { CLICK_SYMBOL } from '../../constants'

// const controls = ['∧', '∨', '¬', '⇒', '⇐', '⇔', '⊤', '⊥']
const Controls = (props) =>
  <div className={styles.controls}>
    <h1 className={styles.title}>iProve</h1>
    <div className={styles.controlList}>
      
      <div className={styles.controlBlock}>
        <div className={styles.label}>Binary Rule</div>
        <div className={styles.template}>
          <div className={styles.exprPlaceholder}></div>
          <div className={styles.symbolPlaceholder}>?</div>
          <div className={styles.exprPlaceholder}></div>
        </div>
      </div>

      <div className={styles.controlBlock}>
        <div className={styles.label}>Unary Rule</div>
        <div className={styles.template}>
          <div className={styles.symbolPlaceholder}>?</div>
          <div className={styles.exprPlaceholder}></div>
        </div>
      </div>

      <div className={styles.controlBlock}>
        <div className={styles.label}>Literal</div>
        <div className={styles.template}>
          <div className={styles.symbolPlaceholder}>x</div>
        </div>
      </div>

      <div className={styles.controlBlock}>
        <div className={styles.label}>True</div>
        <div className={styles.template}>
          <div className={styles.symbolPlaceholder}>⊤</div>
        </div>
      </div>

      <div className={styles.controlBlock}>
        <div className={styles.label}>False</div>
        <div className={styles.template}>
          <div className={styles.symbolPlaceholder}>⊥</div>
        </div>
      </div>

    </div>
  </div>

const mapDispatchToProps = dispatch => {
  return {
    clickSymbol: (symbol) => dispatch({ type: CLICK_SYMBOL, payload: symbol })
  }
}

export default connect(null, mapDispatchToProps)(Controls)