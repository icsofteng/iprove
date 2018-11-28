import React from 'react'
import TextBox from '../TextBox'
import ScopeBox from '../ScopeBox'
import styles from './styles.scss'

const assumeScope = (steps, offset, props, textboxes, i, caseNumber) => {
  let s = steps[i]
  let findExit
  for (findExit = i; findExit < steps.length; findExit++) {
    if (!is_subscope(steps[findExit].scope, s.scope)) {
      break
    }
  }
  const insideSteps = steps.slice(i+1, findExit)
  textboxes.push(
    <ScopeBox start={i+offset+props.start+1} end={findExit+offset+props.start} firstAst={s.ast} caseNumber={caseNumber>-1 ? caseNumber : null}>
      {stepToTextBox(s, i + offset, props)}
      {generateTextBoxScopes(insideSteps, i + offset + 1, props)}
    </ScopeBox>
  )
  return findExit
}

const caseScope = (steps, offset, props, textboxes, i) => {
  let s = steps[i]
  let findExit
  for (findExit = i; findExit < steps.length; findExit++) {
    if (!is_subscope(steps[findExit].scope, s.scope)) {
      break
    }
  }
  const insideSteps = steps.slice(i+1, findExit)
  textboxes.push(
    <ScopeBox start={i+offset+props.start+1} end={findExit+offset+props.start} firstAst={s.ast} setSelected={props.setSelected} isCase>
      {stepToTextBox(s, i + offset, props)}
      {generateTextBoxScopes(insideSteps, i + offset + 1, props, true)}
    </ScopeBox>
  )
  return findExit
}

const generateTextBoxScopes = (steps, offset, props, isCase = false) => {
  let i = 0
  const textboxes = []
  let caseNumber = 1
  while (i < steps.length) {
    let s = steps[i]
    if (s.ast.type === 'assume') {
      i = assumeScope(steps, offset, props, textboxes, i, isCase ? caseNumber : -1)
      caseNumber++
    }
    else if (s.ast.type === 'case') {
      i = caseScope(steps, offset, props, textboxes, i)
    }
    else {
      textboxes.push(stepToTextBox(s, i + offset, props))
      i++
    }
  }
  return textboxes
}

const is_subscope = (inner, outer) => outer.every(i => inner.indexOf(i) > -1)

const stepToTextBox = (step, id, props) =>
  <TextBox
    key={"step"+id}
    ast={step.ast}
    scope={step.scope || []}
    dependencies={step.dependencies}
    index={id}
    focus={props.type === props.selectedTextBox[0] && id === props.selectedTextBox[1]}
    onIncInput={props.incrementInput}
    newStepAfter={props.newStepAfter}
    removeCurrentStep={props.removeCurrentStep}
    onFocus={()=>props.setSelected([props.type, id])}
    onBlur={()=>props.setSelected(['', -1])}
    type={props.type}
    showDependencies={props.showDependencies}
    offset={props.start}
    z3={props.z3[id]}
  />

const TextBoxList = (props) => 
  <div className={styles.steps}>
    { generateTextBoxScopes(props.steps, 0, props) }
  </div>


export default TextBoxList
