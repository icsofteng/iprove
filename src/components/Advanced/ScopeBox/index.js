import React, { Component } from 'react'
import cx from 'classnames'
import { translate_rule as translate_latex } from '../../../translator/latex'
import Latex from 'react-latex'
import styles from './styles.scss'

export default class ScopeBox extends Component {
  constructor() {
    super()
    this.state = { expand: true }
  }
  render() {
    return (
      <div className={cx(styles.scopeBox, {
        [styles.caseScopeBox]: Boolean(this.props.case)
      })}>
        <div className={styles.caseCollapseExpand} onClick={() => this.setState({ expand: !this.state.expand })}>
          { this.state.expand ? "-" : "+" }
        </div>
        { this.state.expand ?
          this.props.children :
          <div className={styles.scopeSummary}>
            {this.props.case && "[Case "+this.props.case+"] "}
            {this.props.start}
            {
              (this.props.end > this.props.start) &&
              "-" + this.props.end
            }: <Latex>{"$"+translate_latex(this.props.firstAst)+"$"}</Latex>
          </div>
        }
      </div>
    )
  }
}