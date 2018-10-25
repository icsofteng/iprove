import React, { Component } from 'react'
import Controls from './Basic/Controls'
import ProofStepList from './Basic/ProofStepList'
import DragDrop from './Basic/DragDrop'
import TextBoxList from './Advanced/TextBoxList'
import { connect } from 'react-redux'
import styles from './styles.scss'

class IProve extends Component {
  constructor(props) {
    super(props)
    this.state = { z3: "", simple: false }
  }

  getRequiredSteps(steps) {
    const stepToCheck = steps[steps.length - 1]
    const { dependencies: goalDependencies } = stepToCheck
    let dependencies = []

    if (goalDependencies) {
      const uncheckedDependencies = goalDependencies.slice(0).filter(Boolean)

      while (uncheckedDependencies.length > 0) {
        const dependency = uncheckedDependencies[0]

        if (dependency >= 0 || dependency <= steps.length) {
          const step = steps[dependency - 1]

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

  render() {
    return (
      <div className="IProve">
        <div className={styles.header}>
          <h1 className={styles.title}>iProve</h1>
          <p>
            Mode: <strong>{this.state.simple ? "Basic" : "Advanced"}</strong>
            <button onClick={()=>this.setState(state => ({ simple: !state.simple}))}>Switch</button>
          </p>
          { this.state.simple && <DragDrop /> }
          { this.state.simple && <Controls /> }
        </div>
        { this.state.simple ?
        <ProofStepList z3={this.state.z3} steps={this.props.steps.filter(s => s.ast.type)} />
        : <TextBoxList steps={this.props.steps} /> }
      </div>
    )
  }
}

export default connect(state => state)(IProve)
