import React, { Component } from 'react'
import Controls from './Basic/Controls'
import ProofStepList from './Basic/ProofStepList'
import DragDrop from './Basic/DragDrop'
import TextBoxList from './Advanced/TextBoxList'
import { connect } from 'react-redux'
import { NEW_STEP } from '../constants'
import styles from './styles.scss'

class IProve extends Component {
  constructor(props) {
    super(props)
    this.state = {
      z3: "",
      simple: false,
      selectedTextBox: ["givens", 0]
    }
  }

  callZ3(steps, constants) {
    fetch('/z3', {
      method: "POST",
      headers: {"Content-Type": "application/json; charset=utf-8"},
      body: JSON.stringify({ steps, constants, relations: [] })
    }).then(r => r.text()).then(response => {
      this.setState({ z3: response.replace(/(\r\n\t|\n|\r\t)/gm, "") })
    })
  }

  getRequiredSteps() {
    const { constants, steps, givens } = this.props
    steps.forEach(step => {
      if (step.dependencies && step.dependencies.length > 0) {
        let requiredSteps = step.dependencies.map(d => {
          if (d <= givens.length) {
            return givens[d-1].ast
          }
          else {
            return steps[d-givens.length-1].ast
          }
        })
        requiredSteps.push(step.ast)
        this.callZ3(requiredSteps, constants)
      }
    })
  }
  
  componentDidUpdate(prevProps) {
    if (prevProps.steps !== this.props.steps) {
      this.getRequiredSteps()
    }
  }

  incrementInput = (v) => {
    const sameSelectedType = this.state.selectedTextBox[0]
    const newSelected = this.state.selectedTextBox[1] + v
    this.setState({ selectedTextBox: [sameSelectedType, newSelected] })
    if (newSelected === this.props[sameSelectedType].length) {
      this.props.newStep([sameSelectedType, newSelected])
    }
  }

  render() {
    return (
      <div className={styles.iprove}>
        <div className={styles.header}>
          <h1 className={styles.title}>iProve</h1>
          <p>
            Mode: <strong>{this.state.simple ? "Basic" : "Advanced"}</strong>
            <button onClick={()=>this.setState(state => ({ simple: !state.simple}))}>Switch</button>
          </p>
          { this.state.simple && <DragDrop /> }
          { this.state.simple && <Controls /> }
        </div>
        <div className={styles.panels}>
          <div className={styles.leftPanel}>
            <div className={styles.panelBox}>
              <div className={styles.panelTitle}>Givens</div>
              <div className={styles.panelContent}>
                { this.state.simple ?
                      <ProofStepList z3={this.state.z3} start={0} steps={this.props.givens} />
                    : <TextBoxList z3={this.state.z3} start={0} steps={this.props.givens} type="givens" selectedTextBox={this.state.selectedTextBox} setSelected={(v)=>this.setState({ selectedTextBox: v })} incrementInput={this.incrementInput} />
                }
              </div>
            </div>
            <div className={styles.panelBox}>
              <div className={styles.panelTitle}>Goal</div>
              <div className={styles.panelContent}>
              </div>
            </div>
          </div>
          <div className={styles.rightPanel}>
            <div className={styles.panelBox}>
              <div className={styles.panelTitle}>Proof</div>
              <div className={styles.panelContent}>
                { this.state.simple ?
                    <ProofStepList z3={this.state.z3} steps={this.props.steps} start={this.props.givens.length} showDependencies />
                  : <TextBoxList z3={this.state.z3} steps={this.props.steps} start={this.props.givens.length} showDependencies type="steps" selectedTextBox={this.state.selectedTextBox} setSelected={(v)=>this.setState({ selectedTextBox: v })} incrementInput={this.incrementInput} />
                }
              </div>
            </div>
          </div>
        </div>
      </div>
    )
  }
}

const mapDispatchToProps = dispatch => ({
  newStep: (path) => dispatch({ type: NEW_STEP, path })
})

export default connect(state => state, mapDispatchToProps)(IProve)
