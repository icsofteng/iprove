import React from 'react'
import { connect } from 'react-redux'
import TextBox from '../TextBox'
import ScopeBox from '../ScopeBox'
import { findScope } from '../../../utils/scopes'
import styles from './styles.scss'

const generateTextBoxScopes = (props, offset = 0, isCase = false) => {
  let i = 0
  const textboxes = []
  let caseNumber = 1
  const steps = props[props.type]
  while (i < steps.length) {
    let s = steps[i]
    if (s.ast.type === 'assume') {
      let findExit = findScope(props, i)
      const insideSteps = steps.slice(i+1, findExit)
      textboxes.push(
        <ScopeBox start={i+offset+props.firstLineNumber+1} end={findExit+offset+props.firstLineNumber} firstAst={s.ast} caseNumber={isCase ? caseNumber : null}>
          {stepToTextBox(s, i + offset, props)}
          {generateTextBoxScopes(insideSteps, i + offset + 1, props)}
        </ScopeBox>
      )
      i = findExit
      caseNumber++
    }
    else if (s.ast.type === 'case') {
      let findExit = findScope(props, i)
      const insideSteps = steps.slice(i+1, findExit)
      textboxes.push(
        <ScopeBox start={i+offset+props.firstLineNumber+1} end={findExit+offset+props.firstLineNumber} firstAst={s.ast} isCase>
          {stepToTextBox(s, i + offset, props)}
          {generateTextBoxScopes(insideSteps, i + offset + 1, props, true)}
        </ScopeBox>
      )
    }
    else {
      textboxes.push(stepToTextBox(s, i + offset, props))
      i++
    }
  }
  return textboxes
}

const stepToTextBox = (step, index, props) =>
  <TextBox step={step} index={index} {...props} />

const TextBoxList = (props) => 
  <div className={styles.steps}>
    { generateTextBoxScopes(props) }
  </div>

const mapStateToProps = ({ present: { goal, steps, givens } }) => {
  return { goal, steps, givens }
}

export default connect(mapStateToProps, null)(TextBoxList)