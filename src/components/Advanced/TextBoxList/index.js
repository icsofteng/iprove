import React, { Component } from 'react'
import TextBox from '../TextBox'
import styles from './styles.scss'
import { NEW_STEP } from '../../../constants';
import { connect } from 'react-redux';

class TextBoxList extends Component {
  constructor() {
    super()
    this.state = { selected: 0 }
  }

  incrementInput = (v) => {
    const newSelected = this.state.selected + v
    this.setState({ selected: newSelected })
    if (newSelected === this.props.steps.length) {
      this.props.newStep([newSelected])
    }
  }
  
  render() { 
    return (
      <div className={styles.steps}>
        {
          this.props.steps.map((step, id) =>
            <TextBox
              key={"step"+id}
              ast={step.ast}
              dependencies={step.dependencies}
              index={id}
              focus={id === this.state.selected}
              onIncInput={this.incrementInput}
              onFocus={()=>this.setState({ selected: id })}
            />
          )
        }
      </div>
    )
  }
}

const mapDispatchToProps = dispatch => ({
  newStep: (path) => dispatch({ type: NEW_STEP, path })
})

export default connect(null, mapDispatchToProps)(TextBoxList)