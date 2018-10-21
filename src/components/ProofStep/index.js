import React, { Component } from 'react'
import MathJax from 'react-mathjax'
import cx from 'classnames'

import { translate_rule } from '../../translator/mathjax'

import Rule from '../Rule'
import StepDependencies from '../StepDependencies'

import styles from './styles.scss'

export default class ProofStep extends Component {
  constructor(props) {
    super(props)
    this.state = { mathjax: false }
  }

  render() {
    const { rule, index } = this.props
    return (
      <React.Fragment>
        <div className={styles.step}>
          <div className={styles.lineNumber}>{index + 1}</div>
          <div className={cx(styles.mathjax, {[styles.showMathjax]: this.state.mathjax})}>
            <MathJax.Provider>
              <MathJax.Node formula={translate_rule(this.props.rule)} />
            </MathJax.Provider>
          </div>
          {
            !this.state.mathjax &&
            <Rule key={"rule" + index} {...rule} path={[index]} />
          }
          <button onClick={()=>this.setState(state => ({ mathjax: !state.mathjax }))}>Toggle</button>
          <StepDependencies index={index} rule={rule} path={[index]} />
        </div>
      </React.Fragment>
    )
  }
}
