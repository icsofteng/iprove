import React, { Component } from 'react'
import Latex from 'react-latex'
import cx from 'classnames'
import { translate_rule } from '../../../translator/latex'
import Rule from '../Rule'
import DependencyList from '../DependencyList'
import styles from './styles.scss'

export default class ProofStep extends Component {
  constructor(props) {
    super(props)
    this.state = { latex: false }
  }

  render() {
    const { step, index, showDependencies, offset, type } = this.props
    return (
      <React.Fragment>
        <div className={styles.step}>
          { type !== 'goal' && <div className={styles.lineNumber}>{offset + index + 1}</div> }
          <div className={cx(styles.latex, {[styles.showLatex]: this.state.latex})}>
            <Latex>{"$"+translate_rule(step.ast)+"$"}</Latex>
          </div>
          {
            !this.state.latex &&
            <div className={styles.proofStep}>
              <Rule key={"rule" + index} {...step.ast} path={[type, index, "ast"]} />
            </div>
          }
          <button onClick={()=>this.setState(state => ({ latex: !state.latex }))}>Toggle</button>
        { showDependencies && <DependencyList index={index} dependencies={step.dependencies} path={[type, index, "dependencies"]} /> }
        </div>
      </React.Fragment>
    )
  }
}
