import React from 'react'
import TextBox from '../TextBox'
import ScopeBox from '../ScopeBox'
import styles from './styles.scss'

const generateTextBoxScopes = (steps, offset, props) => {
  let i = 0
  const textboxes = []
  while (i < steps.length) {
    let s = steps[i]
    if (s.ast.type === 'assume') {
      let findExit
      for (findExit = i; findExit < steps.length; findExit++) {
        if (!is_subscope(steps[findExit].scope, s.scope)) {
          break
        }
      }
      const insideSteps = steps.slice(i+1, findExit)
      textboxes.push(
        <ScopeBox scope={s.scope}>
          {stepToTextBox(s, i + offset, props)}
          {generateTextBoxScopes(insideSteps, i + offset + 1, props)}
        </ScopeBox>
      )
      i = findExit
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