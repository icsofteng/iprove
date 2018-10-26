import React from 'react'
import cx from 'classnames'
import styles from './styles.scss'

const RulePlaceholder = ({ wide, path, dropLiteral }) =>
  <div
    className={cx('dropzone', styles.rulePlaceholder, {
      wide: wide
    })}
    data-path={JSON.stringify(path)}
    onClick={() => !wide && dropLiteral(path)}
  >
    { wide && "Drag a step here to add it to your proof." }
  </div>

export default RulePlaceholder
