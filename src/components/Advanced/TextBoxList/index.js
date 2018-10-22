import React, { Component } from 'react'
import TextBox from '../TextBox'
import styles from './styles.scss'

export default class TextBoxList extends Component {
  constructor() {
    super()
    this.state = { selected: 0 }
  }
  
  render() { 
    return (
      <div className={styles.steps}>
        {
          this.props.steps.concat({}).map((rule, id) =>
            <TextBox
              key={"step"+id}
              rule={rule}
              index={id}
              focus={id === this.state.selected}
              onIncInput={(v)=>this.setState(state => ({ selected: state.selected+v }))}
              onFocus={()=>this.setState({ selected: id })}
            />
          )
        }
      </div>
    )
  }
}

