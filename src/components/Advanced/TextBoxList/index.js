import React from 'react'
import TextBox from '../TextBox'
import styles from './styles.scss'

const TextBoxList = (props) =>
  <div className={styles.steps}>
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
          type={props.type}
          showDependencies={props.showDependencies}
          offset={props.start}
        />
      )
    }
  </div>



export default TextBoxList