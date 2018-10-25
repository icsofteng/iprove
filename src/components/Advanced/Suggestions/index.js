import React from 'react'
import cx from 'classnames'
import styles from './styles.scss'

const SuggestionItem = ({ type, label, onHover, selected, charsTyped = 2 }) =>
  <div onMouseEnter={onHover} className={cx(styles.suggestionItem, {
    [styles.suggestionSelected]: selected
  })}>
    <div className={styles.suggestionValue}>
      <span className={styles.typed}>{ label.substr(0, charsTyped) }</span>
      { label.substr(charsTyped) }
    </div>
    <div className={styles.suggestionType}>{type}</div>
  </div>

const Suggestions = ({ selected, onHover }) => {
  const selectedMod = (selected + 4) % 4
  return (
    <div className={styles.suggestionsBox}>
      <SuggestionItem type="binary" label="and" selected={selectedMod===0} onHover={()=>onHover(0)} />
      <SuggestionItem type="binary" label="or" selected={selectedMod===1} onHover={()=>onHover(1)} />
      <SuggestionItem type="binary" label="implies" selected={selectedMod===2} onHover={()=>onHover(2)} />
      <SuggestionItem type="binary" label="iff" selected={selectedMod===3} onHover={()=>onHover(3)} />
    </div>
  )
}

export default Suggestions