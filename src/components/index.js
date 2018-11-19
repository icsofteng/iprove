import React, { Component } from 'react'
import { connect } from 'react-redux'
import _ from 'underscore'
import Controls from './Basic/Controls'
import ProofStepList from './Basic/ProofStepList'
import DragDrop from './Basic/DragDrop'
import TextBoxList from './Advanced/TextBoxList'
import { NEW_STEP, LOAD_PROOF, REMOVE_STEP, INSERT_STEP, SET_CURRENT_SCOPE } from '../constants'
import { is_step, validate_dependencies } from '../utils'
import Toolbar from './Shared/Toolbar'
import { saveDialog, openDialog } from './Shared/Toolbar/actions'
import { ActionCreators } from 'redux-undo'
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

  componentDidMount() {
    document.addEventListener('keypress', (e) => {
      if (e.code === 'KeyZ' && e.ctrlKey) {
        this.props.undo()
      }
      else if (e.code === 'KeyY' && e.ctrlKey) {
        this.props.redo()
      }
    })
  }

  callZ3(steps, constants, relations, atoms, i, types) {
    return fetch('/z3', {
      method: "POST",
      headers: { "Content-Type": "application/json; charset=utf-8" },
      body: JSON.stringify({steps, constants, relations, atoms, types})
    }).then(r => r.text()).then(response => {
      return new Promise((resolve, reject) => {
        const currentZ3 = this.state.z3
        currentZ3[i] = response.replace(/(\r\n\t|\n|\r\t)/gm, "")
        this.setState({ z3: currentZ3 }, () => {
          // Check goal
          if (_.isEqual(this.props.goal[0].ast, steps[steps.length - 1])) {
            this.setState({ goalAchieved: [currentZ3[currentZ3.length - 1]] }, () => resolve())
          }
          else {
            resolve()
          }
        })
      })
    })
  }

  callLatex = () => {
    const { givens, steps } = this.props
    fetch('/pdf', {
      method: "POST",
      headers: {"Content-Type": "application/json; charset=utf-8"},
      body: JSON.stringify({steps, givens}),
    }).then(r => {
      if (r.status === 200) {
        r.blob().then(response => {
          const file = new Blob([response], {type: 'application/pdf'})
          const fileURL = URL.createObjectURL(file)
          const a = document.createElement('a')
          a.download = 'download.pdf'
          a.type = 'application/pdf'
          a.href = fileURL
          a.click()
        })
      }
      else {
        alert("There was a problem exporting this proof to a PDF")
      }
    })
  }

  getRequiredSteps() {
    const { atoms, constants, relations, steps, givens, types } = this.props
    this.setState({ goalAchieved: [] })
    const promises = steps.map((step, i) => {
      if (step.ast.type) {
        let requiredSteps = step.dependencies.filter(Boolean)
                                             .map(d => validate_dependencies(step, d, givens, steps))
                                             .filter(Boolean)
        requiredSteps.push(step.ast)
        return this.callZ3(requiredSteps, constants, relations, atoms, i, types)
      }
      return Promise.resolve()
    })
    return Promise.all(promises)
  }

  componentDidUpdate(prevProps) {
    if (prevProps.steps !== this.props.steps) {
      this.getRequiredSteps()
    }
  }

  incrementInput = (v) => {
    const sameSelectedType = this.state.selectedTextBox[0]
    const newSelected = Math.min(this.state.selectedTextBox[1] + v, this.props[sameSelectedType].length)
    if (v == -1 && (newSelected != -1 || (newSelected == -1 && this.props[sameSelectedType].length != 1))) {
      this.props.removeStep([sameSelectedType, newSelected])
      this.setState({ selectedTextBox: [sameSelectedType, newSelected] })
    } else if (v == 1) {
      this.props.newStep([sameSelectedType, newSelected])
      this.setState({ selectedTextBox: [sameSelectedType, newSelected] })
    }
  }

  newStepAfter = (index) => {
    const sameSelectedType = this.state.selectedTextBox[0]
    this.props.insertStep([sameSelectedType, index + 1])
    this.setState({ selectedTextBox: [sameSelectedType, index + 1] })
  }

  setSelected = (v) => {
    this.setState({ selectedTextBox: v })
    if (this.props[v[0]] && this.props[v[0]][v[1]]) {
      this.props.setCurrentScope(this.props[v[0]][v[1]].scope)
    }
  }

  addNewStep = (v) => {
    const sameSelectedType = this.state.selectedTextBox[0]
    const newSelected = Math.min(this.state.selectedTextBox[1] + v, this.props[sameSelectedType].length)
    this.setState({ selectedTextBox: [sameSelectedType, newSelected] })
    this.props.newStep([sameSelectedType, newSelected])
  }

  render() {
    return (
      <div className={styles.iprove}>
        <Toolbar
          simple={this.state.simple}
          onSave={()=>saveDialog(this.props, this.state)}
          onOpen={()=>openDialog((p, s)=>{this.props.loadProof(p); this.setState(s)})}
          onSwitch={()=>this.setState(state => ({ simple: !state.simple}))}
          onUndo={this.props.undo}
          onRedo={this.props.redo}
          onExportPdf={this.callLatex}
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
                    : <TextBoxList z3={this.state.z3} start={0} steps={this.props.givens} type="givens" selectedTextBox={this.state.selectedTextBox} setSelected={this.setSelected} incrementInput={this.incrementInput} newStepAfter={this.newStepAfter} />
                  }
                </div>
              </div>
              <div className={styles.panelBox}>
                <div className={styles.panelTitle}>Goal</div>
                <div className={styles.panelContent}>
                  { this.state.simple ?
                      <ProofStepList z3={this.state.goalAchieved} steps={this.props.goal} type="goal" />
                    : <TextBoxList z3={this.state.goalAchieved} steps={this.props.goal} type="goal" selectedTextBox={this.state.selectedTextBox} setSelected={this.setSelected} incrementInput={this.incrementInput} />
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
                    : <TextBoxList z3={this.state.z3} steps={this.props.steps} start={this.props.givens.length} showDependencies type="steps" selectedTextBox={this.state.selectedTextBox} setSelected={this.setSelected} incrementInput={this.incrementInput} newStepAfter={this.newStepAfter} />
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
<<<<<<< HEAD
  insertStep: (path) => dispatch({ type: INSERT_STEP, path }),
  removeStep: (path) => dispatch({ type: REMOVE_STEP, path }),
=======
<<<<<<< HEAD
<<<<<<< HEAD
  insertStep: (path) => dispatch({ type: INSERT_STEP, path }),
  removeStep: (path) => dispatch({ type: REMOVE_STEP, path }),
=======
  removeStep: (path) => dispatch({ type: REMOVE_RULE, path }),
>>>>>>> Backspace deletes lines
=======
  removeStep: (path) => dispatch({ type: REMOVE_RULE, path }),
>>>>>>> Backspace deletes lines
>>>>>>> Backspace deletes lines
  loadProof: (props) => dispatch({ type: LOAD_PROOF, payload: props, path: [] }),
  undo: () => dispatch(ActionCreators.undo()),
  redo: () => dispatch(ActionCreators.redo()),
  setCurrentScope: (newScope) => dispatch({ type: SET_CURRENT_SCOPE, payload: newScope, path: [] })
})

export default connect(state => state.present, mapDispatchToProps)(IProve)
