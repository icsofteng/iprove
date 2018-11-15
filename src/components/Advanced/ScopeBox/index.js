import React from 'react'
import cx from 'classnames'
import styles from './styles.scss'

export const ScopeBox = (props) =>
  <div className={cx(styles.scopeBox, {
    [styles.caseScopeBox]: props.case
  })}>
    {props.children}
  </div>

export const CaseAnalysis = (props) =>
  <div className={styles.caseAnalysis}>
    {props.children}
  </div>

export default ScopeBox