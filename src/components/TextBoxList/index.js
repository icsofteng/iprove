import React from 'react'
import TextBox from '../TextBox'
import styles from './styles.scss'

const TextBoxList = (props) =>
  <div className={styles.steps}>
    {
      props.steps.concat({}).map((rule, id) =>
        <TextBox key={"step"+id} rule={rule} index={id} />
      )
    }
  </div>

export default TextBoxList

