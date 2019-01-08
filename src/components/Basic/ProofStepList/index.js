import React from 'react'
import ProofStep from '../ProofStep'
import RulePlaceholder from '../RulePlaceholder'
import { is_step } from '../../../utils'

const ProofStepList = (props) => {
  return (
    <React.Fragment>
      {
        props.steps.filter(is_step).map((step, id) =>
          <ProofStep key={"step"+id} step={step} index={id} showDependencies={props.showDependencies} offset={props.start} type={props.type} z3={props.z3[id]} />
        )
      }
      <div className="proof-line">
        {
          ((props.type === 'goal' && props.steps.filter(is_step).length === 0) || props.type !== 'goal') &&
            <RulePlaceholder wide path={[props.type, props.steps.filter(is_step).length]} />
        }
        <div className="proof-feedback"></div>
      </div>
    </React.Fragment>
  )
}

export default ProofStepList

