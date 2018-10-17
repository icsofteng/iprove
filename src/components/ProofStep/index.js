import React from 'react'
import Rule from '../Rule'
import styles from './styles.scss'

const ProofStep = (props) =>
  <div className={styles.steps}>
    <div className={styles.lineNumber}>{props.index}</div>
    <Rule key={"rule"+props.index} {...props.rule} path={[props.index]} />
  </div>

export default ProofStep