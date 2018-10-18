import React from 'react'
import ProofStep from '../ProofStep'
import cx from 'classnames'
import styles from './styles.scss'
import RulePlaceholder from '../RulePlaceholder'

const numLines = (steps) => {
  let num = 0;
  steps.forEach(step => {
    if (step) num ++;
  });
  return num;
}

const ProofStepList = (props) =>
  <div className={styles.steps}>
    {
      props.z3 &&
      <div className={cx(styles.feedback, {
        [styles.error]: props.z3 !== 'unsat'
      })}>
      {
        numLines(props.steps) <= 1 ? "Please enter more than one step to validate your proof" :
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
      props.steps.map((rule, index) =>
        <ProofStep key={"step"+index} rule={rule} index={numLines(props.steps)} />
      )
    }
    <RulePlaceholder wide path={[props.steps.length]} />
  </div>

export default ProofStepList

