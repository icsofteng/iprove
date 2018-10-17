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
      { props.z3 === 'sat' && "Your proof is incorrect" }
      { props.z3 === 'unsat' && "Your proof is correct, well done!" }
      { props.z3 !== 'sat' && props.z3 !== 'unsat' && "There are errors in your proof" }
      </div>
    }
    {
      props.steps.map((rule, index) =>
        <ProofStep key={"step"+index} rule={rule} index={index} />
      )
    }
    <RulePlaceholder wide path={[props.steps.length]} />
  </div>

export default ProofStepList

