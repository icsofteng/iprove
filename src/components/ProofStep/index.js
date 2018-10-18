import React from 'react'

import Rule from '../Rule'
import StepDependencies from '../StepDependencies'

import styles from './styles.scss'

const ProofStep = ({ index, rule }) =>
  <div className={styles.step}>
    <div className={styles.lineNumber}>{ index + 1 }</div>
    <Rule key={"rule" + index} {...rule} path={[index]} />
    <StepDependencies index={index} rule={rule} path={[index]} />
  </div>

export default ProofStep
