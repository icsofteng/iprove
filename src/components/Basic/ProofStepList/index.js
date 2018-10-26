import React from 'react'
import ProofStep from '../ProofStep'
import styles from './styles.scss'
import RulePlaceholder from '../RulePlaceholder'
import { is_step } from '../../../utils'
import Feedback from '../../Feedback'

const ProofStepList = (props) => {
  return (
    <div className={styles.steps}>
      <Feedback z3={props.z3} steps={props.steps} />
      {
        this.props.steps.filter(is_step).map((step, id) =>
          <ProofStep key={"step"+id} step={step} index={id} showDependencies={props.showDependencies} />
        )
      }
      <RulePlaceholder wide path={[props.steps.length]} />
    </div>
  )
}

export default ProofStepList

