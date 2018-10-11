/* Dependencies */
import React from 'react'
import cx from 'classnames'
import { connect } from 'react-redux'
import Rule from 'components/Rule'
import RuleControls from 'components/RuleControls'
import styles from './styles.scss'

const RuleList = (props) =>
  <React.Fragment>
    <RuleControls />
    <ul className={cx(styles.ruleList)}>
    {
      props.rules.map((rule, index) =>
        <Rule key={"rule"+index} value={rule} index={index} />
      )
    }
  </ul>
  </React.Fragment>

const mapStateToProps = state => {
  return { rules: state.rules.steps }
}

export default connect(mapStateToProps, null)(RuleList)