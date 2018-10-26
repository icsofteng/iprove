import React from 'react'
import TextBox from '../TextBox'
import styles from './styles.scss'
import Feedback from '../../Feedback'

const TextBoxList = (props) =>
  <div className={styles.steps}>
    <Feedback z3={props.z3} steps={props.steps} />
    {
      props.steps.map((step, id) =>
        <TextBox
          key={"step"+id}
          ast={step.ast}
          dependencies={step.dependencies}
          index={id}
          focus={props.type === props.selectedTextBox[0] && id === props.selectedTextBox[1]}
          onIncInput={props.incrementInput}
          onFocus={()=>props.setSelected([props.type, id])}
          showDependencies={props.showDependencies}
          offset={props.start}
        />
      )
    }
  </div>



export default TextBoxList