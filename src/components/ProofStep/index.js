import React, { Component } from 'react'
import Rule from '../Rule'
import MathJax from 'react-mathjax'
import cx from 'classnames'
import { translate_rule } from '../../translator/mathjax'
import styles from './styles.scss'

export default class ProofStep extends Component {
  constructor(props) {
    super(props)
    this.state = { mathjax: false }
  }

  render() {
    return (
      <React.Fragment>
        <div className={styles.step}>
          <div className={styles.lineNumber}>{this.props.index+1}</div>
          <div className={cx(styles.mathjax, {[styles.showMathjax]: this.state.mathjax})}>
            <MathJax.Provider>
              <MathJax.Node formula={translate_rule(this.props.rule)} />
            </MathJax.Provider>
          </div>
          {
            !this.state.mathjax &&
            <Rule key={"rule"+this.props.index} {...this.props.rule} path={[this.props.index]} />
          }
          <button onClick={()=>this.setState(state => ({ mathjax: !state.mathjax }))}>Toggle</button>
        </div>
      </React.Fragment>
    )
  }
}