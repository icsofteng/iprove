import React from 'react'
import TextBox from '../TextBox'
import styles from './styles.scss'

const TextBoxList = (props) => {
  const list = props.steps.concat({})
  return (
    <div className={styles.steps}>
      {
        list.map((rule, id) =>
          <TextBox key={"step"+id} rule={rule} index={id} focus={id === list.length-1} />
        )
      }
    </div>
  )
}

export default TextBoxList

