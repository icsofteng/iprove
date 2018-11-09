import React from 'react'
import TextBox from '../TextBox'
import ScopeBox from '../ScopeBox'
import _ from 'underscore'
import styles from './styles.scss'

const generateTextBoxScopes = (steps, offset, props) => {
  let i = 0
  const textboxes = []
  while (i < steps.length) {
    let s = steps[i]
    if (s.ast.type === 'assume') {
      let findExit
      for (findExit = steps.length-1; findExit > i; findExit--) {
        if (_.isEqual(steps[findExit].scope, s.scope)) {
          break
        }
      }
      const insideSteps = steps.slice(i+1, findExit + 1)
      
      textboxes.push(
        <ScopeBox>
          {stepToTextBox(s, i + offset, props)}
          {generateTextBoxScopes(insideSteps, i+1, props)}
        </ScopeBox>
      )
      i = findExit + 1
    }
    else {
      textboxes.push(stepToTextBox(s, i + offset, props))
      i++
    }
  }
  return textboxes
}

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