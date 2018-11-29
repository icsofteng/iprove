import React from 'react'
import { translate_rule as translate_raw } from '../../../translator/raw'
import styles from './styles.scss'

const EditView = ({ onKeyDown, onFocus, onBlur, onRef, ast }) =>
  <div className={styles.textboxContainer}>
    <input
      type="text"
      defaultValue={translate_raw(ast)}
      className={styles.textbox}
      onKeyDown={onKeyDown}
      onFocus={onFocus}
      onBlur={onBlur}
      ref={onRef}
    />
  </div>

export default EditView