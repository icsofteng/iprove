import React from 'react'
import cx from 'classnames'
import styles from './styles.scss'

const Controls = () =>
  <div className={styles.controlList}>
    
    <div data-type="binary" className={cx('drag-drop', styles.controlBlock)}>
      <div className={styles.label}>Binary Rule</div>
      <div className={styles.template}>
        <div className={styles.exprPlaceholder}></div>
        <div className={styles.symbolPlaceholder}>?</div>
        <div className={styles.exprPlaceholder}></div>
      </div>
    </div>

    <div data-type="unary" className={cx('drag-drop', styles.controlBlock)}>
      <div className={styles.label}>Unary Rule</div>
      <div className={styles.template}>
        <div className={styles.symbolPlaceholder}>?</div>
        <div className={styles.exprPlaceholder}></div>
      </div>
    </div>

    <div data-type="literal" className={cx('drag-drop', styles.controlBlock)}>
      <div className={styles.label}>Literal</div>
      <div className={styles.template}>
        <div className={styles.symbolPlaceholder}>x</div>
      </div>
    </div>

    <div data-type="true" className={cx('drag-drop', styles.controlBlock)}>
      <div className={styles.label}>True</div>
      <div className={styles.template}>
        <div className={styles.symbolPlaceholder}>⊤</div>
      </div>
    </div>

    <div data-type="false" className={cx('drag-drop', styles.controlBlock)}>
      <div className={styles.label}>False</div>
      <div className={styles.template}>
        <div className={styles.symbolPlaceholder}>⊥</div>
      </div>
    </div>

  </div>

export default Controls