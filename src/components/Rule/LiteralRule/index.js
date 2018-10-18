import React from 'react'

import styles from '../styles.scss'

const LiteralRule = (props) =>
  <input
    type="text"
    value={props.value}
    onChange={(event) => {
      props.addConstant(event.target.value)
      props.updateValue([...props.path, "value"], event.target.value)
    }}
    className={styles.ruleInput}
  />

export default LiteralRule
