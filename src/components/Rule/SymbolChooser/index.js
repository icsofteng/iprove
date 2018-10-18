import React from 'react'

import styles from './styles.scss'

const SymbolChooser = ({ updateValue, current, path, symbols }) =>
  <select
    className={styles.ruleSymbol}
    value={current}
    onChange={(event) => updateValue(path, event.target.value)}
  >
    <option>...</option>
    {
      Object.keys(symbols).map((key, i) =>
        <option value={key} key={i}>{symbols[key]}</option>
      )
    }
  </select>

export default SymbolChooser
