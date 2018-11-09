import React, { Component } from 'react'
import styles from './styles.scss'

class ScopeBox extends Component {
  render() {
    return (
      <div className={styles.scopeBox}>
        {this.props.children}
      </div>
    )
  }
}

export default ScopeBox