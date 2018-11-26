import React, { Component } from 'react'
import { translate_rule as translate_latex } from '../../../translator/latex'
import { connect } from 'react-redux'
import Latex from 'react-latex'
import styles from './styles.scss'
import { ADD_CASE } from '../../../constants'

class ScopeBox extends Component {
  constructor() {
    super()
    this.state = { expand: true }
  }
  addCaseStep = () => {
    this.props.addCase(this.props.start, this.props.end)
    this.props.setSelected(["steps", this.props.end - this.props.givens])
  }
  render() {
    return (
      <div className={styles.scopeBox}>
        <div className={styles.caseCollapseExpand} onClick={() => this.setState({ expand: !this.state.expand })}>
          { this.state.expand ? "-" : "+" }
        </div>
        { this.state.expand ?
          <React.Fragment>
            {
              React.Children.map(this.props.children, child =>
                React.cloneElement(child, { parentCase: this.props.caseNumber })
              )
            }
            { this.props.isCase &&
              <div className={styles.newCase} onClick={this.addCaseStep}>
              <i className={styles.addScopeButton}>+</i> Add a new case
            </div>
            }
          </React.Fragment>
          :
          <div className={styles.scopeSummary}>
            {this.props.caseNumber && "[Case "+this.props.caseNumber+"] "}
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

const mapDispatchToProps = dispatch => ({
  addCase: (start, end) => dispatch({ type: ADD_CASE, start, end, path: [] })
})

export default connect(state => ({ givens: state.present.givens.length }), mapDispatchToProps)(ScopeBox)
