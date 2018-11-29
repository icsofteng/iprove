import React from 'react'
import styles from './styles.scss'

const exclude_dependency = (ast) =>
  ast.type === 'assume' || ast.type === 'arbitrary' || ast.type === 'exit' || ast.type === 'case'

const DependencyBox = ({ show, ast, onFocus, onBlur, onRef, value, onKeyDown }) =>
  show && !exclude_dependency(ast) ?
  <div className={styles.dependencies}>
    <div className={styles.using} onClick={()=>this.refDef.focus()}>using</div>
    <input
      type="text"
      className={styles.dependencyTextbox}
      defaultValue={value.join(", ")}
      onKeyDown={onKeyDown}
      onFocus={onFocus}
      onBlur={onBlur}
      ref={onRef}
    />
  </div>
  : null

export default DependencyBox