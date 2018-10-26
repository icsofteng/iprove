import React, { Component } from 'react'
import MathJax from 'react-mathjax'
import cx from 'classnames'
import { translate_rule } from '../../../translator/mathjax'
import Rule from '../Rule'
import DependencyList from '../DependencyList'
import styles from './styles.scss'

export default class ProofStep extends Component {
  constructor(props) {
    super(props)
    this.state = { mathjax: false }
  }

  render() {
    const { step, index } = this.props
    return (
      <React.Fragment>
        <div className={styles.step}>
          <div className={styles.lineNumber}>{index + 1}</div>
          <div className={cx(styles.mathjax, {[styles.showMathjax]: this.state.mathjax})}>
            <MathJax.Provider>
              <MathJax.Node formula={translate_rule(step.ast)} />
            </MathJax.Provider>
          </div>
          {
            !this.state.mathjax &&
            <div className={styles.proofStep}>
              <Rule key={"rule" + index} {...step.ast} path={[index, "ast"]} />
            </div>
          }
          <button onClick={()=>this.setState(state => ({ mathjax: !state.mathjax }))}>Toggle</button>
          <DependencyList index={index} dependencies={step.dependencies} path={[index, "dependencies"]} />
        </div>
      </React.Fragment>
    )
  }
}
