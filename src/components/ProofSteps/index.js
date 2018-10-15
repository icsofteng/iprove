/* Dependencies */
import React from 'react'
import { connect } from 'react-redux'
import Rule from '../Rule'
import styles from './styles.scss'

const ProofSteps = (props) =>
  <div className={styles.steps}>
    {
      props.rules.map((rule, index) =>
        <Rule key={"rule"+index} value={rule} index={index} />
      )
    }
    <div className={styles.rulePlaceholder}>
      Drag a step here to add it to your proof.
    </div>
  </div>

const mapStateToProps = state => {
  return { rules: state.rules.steps }
}

export default connect(mapStateToProps, null)(ProofSteps)