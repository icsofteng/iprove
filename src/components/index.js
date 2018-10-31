import React, { Component } from 'react'
import Controls from './Basic/Controls'
import ProofStepList from './Basic/ProofStepList'
import DragDrop from './Basic/DragDrop'
import TextBoxList from './Advanced/TextBoxList'
import { connect } from 'react-redux'
import { NEW_STEP, LOAD_PROOF } from '../constants'
import { is_step } from '../utils'
import Toolbar from './Shared/Toolbar'
import { saveDialog, openDialog } from './Shared/Toolbar/actions'
import _ from 'underscore'
import styles from './styles.scss'

class IProve extends Component {
  constructor(props) {
    super(props)
    this.state = {
      goalAchieved: [],
      z3: [],
      simple: false,
      selectedTextBox: ["givens", 0]
    }
  }

  callZ3(steps, constants, relations, atoms, i) {
    fetch('/z3', {
      method: "POST",
      headers: {"Content-Type": "application/json; charset=utf-8"},
      body: JSON.stringify({steps, constants, relations, atoms})
    }).then(r => r.text()).then(response => {
      const currentZ3 = this.state.z3
      currentZ3[i] = response.replace(/(\r\n\t|\n|\r\t)/gm, "")
      if (currentZ3 !== "") {
        this.setState({ z3: currentZ3 })
        // Check goal
        if (_.isEqual(this.props.goal[0].ast, steps[steps.length-1])) {
          this.setState({ goalAchieved: [currentZ3[currentZ3.length-1]] })
        }
      }
    })
  }

  getRequiredSteps() {
    const { atoms, constants, relations, steps, givens } = this.props
    this.setState({ goalAchieved: [] })
    steps.forEach((step, i) => {
      if (step.dependencies && step.dependencies.length > 0) {
        let requiredSteps = step.dependencies.filter(Boolean).map(d => {
          if (d <= givens.length) {
            return (givens[d-1] && givens[d-1].ast) || null
          }
          else {
            return (steps[d-givens.length-1] && steps[d-givens.length-1].ast) || null
          }
        }).filter(Boolean)
        requiredSteps.push(step.ast)
        this.callZ3(requiredSteps, constants, relations, atoms, i)
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
        <Toolbar
          simple={this.state.simple}
          onSave={()=>saveDialog(this.props, this.state)}
          onOpen={()=>openDialog((p, s)=>{this.props.loadProof(p); this.setState(s)})}
          onSwitch={()=>this.setState(state => ({ simple: !state.simple}))}
        />
        <div className={styles.header}>
          <h1 className={styles.title}>iProve</h1>
        </div>
        <div className={styles.panels}>
          <div className={styles.leftRightPanel}>
            <div className={styles.leftPanel}>
              <div className={styles.panelBox}>
                <div className={styles.panelTitle}>Givens</div>
                <div className={styles.panelContent}>
                  { this.state.simple ?
                      <ProofStepList z3={this.state.z3} start={0} steps={this.props.givens} type="givens" />
                    : <TextBoxList z3={this.state.z3} start={0} steps={this.props.givens} type="givens" selectedTextBox={this.state.selectedTextBox} setSelected={(v)=>this.setState({ selectedTextBox: v })} incrementInput={this.incrementInput} />
                  }
                </div>
              </div>
              <div className={styles.panelBox}>
                <div className={styles.panelTitle}>Goal</div>
                <div className={styles.panelContent}>
                  { this.state.simple ?
                      <ProofStepList z3={this.state.goalAchieved} steps={this.props.goal} type="goal" />
                    : <TextBoxList z3={this.state.goalAchieved} steps={this.props.goal} type="goal" selectedTextBox={this.state.selectedTextBox} setSelected={(v)=>this.setState({ selectedTextBox: v })} incrementInput={this.incrementInput} />
                  }
                </div>
              </div>
            </div>
            <div className={styles.rightPanel}>
              <div className={styles.panelBox}>
                <div className={styles.panelTitle}>Proof</div>
                <div className={styles.panelContent}>
                  { this.state.simple ?
                      <ProofStepList z3={this.state.z3} steps={this.props.steps} start={this.props.givens.filter(is_step).length} showDependencies type="steps" />
                    : <TextBoxList z3={this.state.z3} steps={this.props.steps} start={this.props.givens.length} showDependencies type="steps" selectedTextBox={this.state.selectedTextBox} setSelected={(v)=>this.setState({ selectedTextBox: v })} incrementInput={this.incrementInput} />
                  }
                </div>
              </div>
            </div>
          </div>
          { this.state.simple && <DragDrop /> }
          { this.state.simple && <Controls /> }
        </div>
      </div>
    )
  }
}

const mapDispatchToProps = dispatch => ({
  newStep: (path) => dispatch({ type: NEW_STEP, path }),
  loadProof: (props) => dispatch({ type: LOAD_PROOF, payload: props, path: [] })
})

export default connect(state => state, mapDispatchToProps)(IProve)
