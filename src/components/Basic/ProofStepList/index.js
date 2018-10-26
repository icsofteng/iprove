import React from 'react'
import ProofStep from '../ProofStep'
import styles from './styles.scss'
import RulePlaceholder from '../RulePlaceholder'
import Feedback from '../../Feedback'

const ProofStepList = (props) =>
  <div className={styles.steps}>
    <Feedback z3={props.z3} steps={props.steps} />
    {
      props.steps.filter(Boolean).map((step, id) =>
        <ProofStep key={"step"+id} step={step} index={id} />
      )
    }
    <RulePlaceholder wide path={[props.steps.length]} />
  </div>

export default ProofStepList

