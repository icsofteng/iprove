import React from 'react'
import styles from './styles.scss'

export const ScopeBox = (props) =>
  <div className={styles.scopeBox}>
    {props.children}
  </div>

export const CaseAnalysis = (props) =>
  <div className={styles.caseAnalysis}>
    {props.children}
  </div>

export default ScopeBox