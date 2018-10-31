import React from 'react'
import cx from 'classnames'
import styles from './styles.scss'

const RulePlaceholder = (props) =>
  <div
    className={cx('dropzone', styles.rulePlaceholder, {
      wide: props.wide
    })}
    data-path={JSON.stringify(props.path)}
    onClick={()=>!props.wide && props.dropLiteral(props.path)}
  >
    { props.wide && "Drag a step here to add it to your proof." }
  </div>

export default RulePlaceholder
