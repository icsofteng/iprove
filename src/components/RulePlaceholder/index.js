import React from 'react'
import { connect } from 'react-redux'
import cx from 'classnames'
import styles from './styles.scss'

const RulePlaceholder = (props) =>
  <div
    className={cx('dropzone', styles.rulePlaceholder, {
      [styles.wide]: props.wide
    })}
    data-path={JSON.stringify(props.path)}
    onChange={(event)=>props.dropRule(props.index, event.target.value)}
  >
    { props.wide && "Drag a step here to add it to your proof." }
  </div>

const mapDispatchToProps = dispatch => {
  return {
  }
}

export default connect(null, mapDispatchToProps)(RulePlaceholder)