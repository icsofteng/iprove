import React, { Component } from 'react'
import Controls from './Basic/Controls'
import ProofStepList from './Basic/ProofStepList'
import DragDrop from './Basic/DragDrop'
import TextBoxList from './Advanced/TextBoxList'
import { connect } from 'react-redux'
import { is_step } from '../utils'
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

  getRequiredSteps(steps) {
    const filteredSteps = steps.filter(is_step)
    if (filteredSteps.length > 1) {
      const stepToCheck = filteredSteps[filteredSteps.length - 1]
      const { dependencies: goalDependencies } = stepToCheck
      let dependencies = []

      if (goalDependencies) {
        const uncheckedDependencies = goalDependencies.slice(0).filter(Boolean)

        while (uncheckedDependencies.length > 0) {
          const dependency = uncheckedDependencies[0]

          if (dependency >= 0 || dependency <= filteredSteps.length) {
            const step = filteredSteps[dependency - 1]

            if (step.dependencies) {
              step.dependencies.map(dep => {
                if (!uncheckedDependencies.includes(dep)) {
                  uncheckedDependencies.push(dep)
                }
              })
            }

            dependencies.unshift(step)
          }

          uncheckedDependencies.shift()
        }
      }

      const allSteps = [stepToCheck]
      allSteps.unshift(...dependencies)

      return allSteps
    }
    return []
  }
  
  componentDidUpdate(prevProps) {
    if (prevProps.steps !== this.props.steps) {
      const { steps, constants } = this.props
      const requiredSteps = this.getRequiredSteps(steps)

      fetch('/z3', {
        method: "POST",
        headers: {"Content-Type": "application/json; charset=utf-8"},
        body: JSON.stringify({ steps: requiredSteps, constants, relations: [] })
      }).then(r => r.text()).then(response => {
        this.setState({ z3: response.replace(/(\r\n\t|\n|\r\t)/gm, "") })
      })
    }
  }

  incrementInput = (v) => {
    const sameSelectedType = this.state.selectedTextBox[0]
    const newSelected = this.state.selectedTextBox[1] + v
    this.setState({ selectedTextBox: [sameSelectedType, newSelected] })
    if (newSelected === this.props[sameSelectedType].length) {
      this.props.newStep([newSelected], sameSelectedType)
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
  newStep: (path, key) => dispatch({ type: NEW_STEP, path, key })
})

export default connect(state => state, mapDispatchToProps)(IProve)
