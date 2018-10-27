import React from 'react'
import ProofStep from '../ProofStep'
import styles from './styles.scss'
import RulePlaceholder from '../RulePlaceholder'
import { is_step } from '../../../utils'

const ProofStepList = (props) => {
  return (
    <div className={styles.steps}>
      {
        props.steps.filter(is_step).map((step, id) =>
          <ProofStep key={"step"+id} step={step} index={id} showDependencies={props.showDependencies} offset={props.start} type={props.type} />
        )
      }
      <RulePlaceholder wide path={[props.type, props.steps.filter(is_step).length]} />
    </div>
  )
}

export default ProofStepList

