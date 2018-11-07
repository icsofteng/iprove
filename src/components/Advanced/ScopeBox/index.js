import React, { Component } from 'react'
import TextBoxList from '../TextBoxList'
import styles from './styles.scss'

class ScopeBox extends Component {

  render() {
    return (
      <TextBoxList {...this.props}/>
    )
  }
}

export default ScopeBox