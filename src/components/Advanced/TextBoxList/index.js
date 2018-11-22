import React from 'react'
import TextBox from '../TextBox'
import ScopeBox from '../ScopeBox'
import styles from './styles.scss'

const assumeScope = (steps, offset, props, textboxes, i) => {
  let s = steps[i]
  let findExit
  for (findExit = i; findExit < steps.length; findExit++) {
    if (!is_subscope(steps[findExit].scope, s.scope)) {
      break
    }
  }
  const insideSteps = steps.slice(i+1, findExit)
  textboxes.push(
    <ScopeBox start={i+offset+props.start+1} end={findExit+offset+props.start} firstAst={s.ast}>
      {stepToTextBox(s, i + offset, props)}
      {generateTextBoxScopes(insideSteps, i + offset + 1, props)}
    </ScopeBox>
  )
  return findExit
}

const caseScope = (steps, offset, props, textboxes, i) => {
  let findSwitch
  for (findSwitch = i+1; findSwitch < steps.length; findSwitch++) {
    if (!is_subscope(steps[findSwitch].scope, steps[i+1].scope)) {
      break
    }
  }
  const assume1 = steps[i+1]
  const case1 = steps.slice(i+2, findSwitch)
  if (!steps[findSwitch]) return i+1
  let findEnd
  for (findEnd = findSwitch; findEnd < steps.length; findEnd++) {
    if (!is_subscope(steps[findEnd].scope, steps[findSwitch].scope)) {
      break
    }
  }
  const assume2 = steps[findSwitch]
  const case2 = steps.slice(findSwitch+1, findEnd)
  textboxes.push(
    <ScopeBox start={i+offset+props.start+1} end={findEnd+offset+props.start} firstAst={steps[i].ast}>
      <div className={styles.case_step}>
        {stepToTextBox(steps[i], i + offset, props)}
      </div>
      <ScopeBox case={1} start={i+offset+props.start+2} end={findSwitch+offset+props.start} firstAst={assume1.ast}>
        {stepToTextBox(assume1, i + offset + 1, props)}
        {generateTextBoxScopes(case1, i + offset + 2, props)}
      </ScopeBox>
      <ScopeBox case={2} start={findSwitch+offset+props.start+1} end={findEnd+offset+props.start} firstAst={assume2.ast}>
        {stepToTextBox(assume2, findSwitch + offset, props)}
        {generateTextBoxScopes(case2, findSwitch + offset + 1, props)}
      </ScopeBox>
    </ScopeBox>
  )
  return findEnd
}

const generateTextBoxScopes = (steps, offset, props) => {
  let i = 0
  const textboxes = []
  while (i < steps.length) {
    let s = steps[i]
    if (s.ast.type === 'assume') {
      i = assumeScope(steps, offset, props, textboxes, i)
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
