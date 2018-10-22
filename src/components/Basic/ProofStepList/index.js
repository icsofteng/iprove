import React from 'react'
import ProofStep from '../ProofStep'
import cx from 'classnames'
import styles from './styles.scss'
import RulePlaceholder from '../RulePlaceholder'

const ProofStepList = (props) =>
  <div className={styles.steps}>
    {
      props.z3 &&
      <div className={cx(styles.feedback, {
        [styles.error]: props.z3 !== 'unsat'
      })}>
      {
        props.steps.length <= 1 ? "Please enter more than one step to validate your proof" :
        (props.z3 === 'sat' ? "Your proof is incorrect" :
          (
            props.z3 === 'unsat' ? "Your proof is correct, well done!" :
            "There are errors in your proof"
          )
        )
      }
      </div>
    }
    {
      props.steps.map((rule, id) =>
        <ProofStep key={"step"+id} rule={rule} index={id} />
      )
    }
    <RulePlaceholder wide path={[props.steps.length]} />
  </div>

export default ProofStepList

