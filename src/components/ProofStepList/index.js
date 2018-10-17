import React from 'react'
import ProofStep from '../ProofStep'
import styles from './styles.scss'
import RulePlaceholder from '../RulePlaceholder'

const ProofStepList = (props) =>
  <div className={styles.steps}>
    {
      props.steps.map((rule, index) =>
        <ProofStep key={"step"+index} rule={rule} index={index} />
      )
    }
    <RulePlaceholder wide path={[props.steps.length]} />
  </div>

export default ProofStepList

