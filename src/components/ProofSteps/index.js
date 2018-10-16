import React from 'react'
import { connect } from 'react-redux'
import Rule from '../Rule'
import styles from './styles.scss'
import RulePlaceholder from '../RulePlaceholder'

const ProofSteps = (props) =>
  <div className={styles.steps}>
    {
      props.steps.map((rule, index) =>
        <Rule key={"rule"+index} {...rule} path={[index]} />
      )
    }
    <RulePlaceholder wide path={[props.steps.length]} />
  </div>

const mapStateToProps = state => {
  return { steps: state.steps }
}

export default connect(mapStateToProps, null)(ProofSteps)