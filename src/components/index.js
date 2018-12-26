import React, { Component } from 'react'
import { connect } from 'react-redux'
import _ from 'underscore'
import { ActionCreators } from 'redux-undo'
import Controls from './Basic/Controls'
import ProofStepList from './Basic/ProofStepList'
import DragDrop from './Basic/DragDrop'
import TextBoxList from './Advanced/TextBoxList'
import { saveDialog, openDialog } from './Shared/Toolbar/actions'

import {
  NEW_STEP,
  LOAD_PROOF,
  REMOVE_STEP,
  CLEAR_PROOF,
  BEAUTIFY,
  SET_STEP_DEPENDENCY,
  ADD_LEMMAS,
  SET_Z3,
  SET_GOAL_ACHIEVED,
} from '../constants'
import { is_step, validate_step_dependencies } from '../utils'

const PROOF_EXTENSION = '.proof'
const LEMMAS_EXTENSION = '.lemmas'

class IProve extends Component {
  constructor(props) {
    super(props)
    this.state = {
      simple: false,
      selectedTextBox: ["givens", 0]
    }
  }

  componentDidMount() {
    document.addEventListener('keypress', (e) => {
      if ((e.code === 'KeyZ' && e.ctrlKey) || (e.code === 'KeyZ' && e.metaKey)) {
        e.preventDefault()
        this.props.undo()
      }
      else if ((e.code === 'KeyY' && e.ctrlKey) || (e.code === 'KeyY' && e.metaKey)) {
        e.preventDefault()
        this.props.redo()
      }
    })
  }

  updateStateZ3(steps, identifiers, relations, types, functions, i) {
    const promise = this.callZ3(steps, identifiers, relations, types, functions, i)
    return promise.then((response) => {
      return new Promise((resolve, reject) => {
        const currentZ3 = this.props.z3
        currentZ3[i] = response.trim()
        this.props.setZ3(currentZ3)
        // Check goal
        if (_.isEqual(this.props.goal[0].ast, this.props.steps[this.props.steps.length - 1].ast)) {
          this.props.setGoalAchieved([currentZ3[currentZ3.length - 1]])
        }
        resolve()
      })
    })

  }

  callZ3(steps, identifiers, relations, types, functions, i) {
    return fetch('/z3', {
      method: "POST",
      headers: { "Content-Type": "application/json; charset=utf-8" },
      body: JSON.stringify({steps, identifiers, relations, types, functions })
    }).then(r => r.text())
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
    const { identifiers, relations, steps, givens, types, functions, lemmas } = this.props
    this.props.setGoalAchieved([])
    const promises = steps.map((step, i) => {
      if (step.ast.type) {
        let dependenciesNoRanges = []
        step.dependencies.forEach(d => {
          if (d.toString().indexOf("..") > -1) {
            const startRange = parseInt(d.split("..")[0])
            const endRange = parseInt(d.split("..")[1])
            for (let j=startRange; j<=endRange; j++) {
              dependenciesNoRanges.push(j)
            }
          }
          else if (typeof d === 'string' && d.substr(0, 1).toLowerCase() === 'l') {
            dependenciesNoRanges.push(d)
          }
          else {
            dependenciesNoRanges.push(parseInt(d))
          }
        })
        let requiredSteps = validate_step_dependencies(step, dependenciesNoRanges, givens, steps, lemmas)
        requiredSteps.push(step.ast)
        return this.updateStateZ3(requiredSteps, identifiers, relations, types, functions, i)
      }
      return Promise.resolve()
    })
    return Promise.all(promises)
  }

  componentDidUpdate(prevProps) {
    if (!_.isEqual(prevProps.steps, this.props.steps) || !_.isEqual(prevProps.givens, this.props.givens)  || !_.isEqual(prevProps.goal, this.props.goal)) {
      this.getRequiredSteps()
    }
  }

  incrementInput = (v) => {
    const sameSelectedType = this.state.selectedTextBox[0]
    const newSelected = Math.min(this.state.selectedTextBox[1] + v, this.props[sameSelectedType].length)
    this.setState({ selectedTextBox: [sameSelectedType, newSelected] })
    if (newSelected === this.props[sameSelectedType].length) {
      this.props.newStep([sameSelectedType, newSelected])
    }
  }

  removeCurrentStep = (index) => {
    const absIndex = this.state.selectedTextBox[0] == 'givens' ? index : index + this.props.givens.length
    const sameSelectedType = this.state.selectedTextBox[0]
    if (index !== 0 || (index === 0 && this.props[sameSelectedType].length !== 1)) {
      this.updateDependenciesFromInsertionAndRemoval(absIndex, -1)
      this.props.removeStep([sameSelectedType, index])
      this.setState({ selectedTextBox: [sameSelectedType, index - 1] })
    }
  }

  newStepAfter = (index) => {
    const absIndex = this.state.selectedTextBox[0] == 'givens' ? index : index + this.props.givens.length
    const sameSelectedType = this.state.selectedTextBox[0]
    this.updateDependenciesFromInsertionAndRemoval(absIndex, 1)
    this.props.newStep([sameSelectedType, index + 1])
    this.setState({ selectedTextBox: [sameSelectedType, index + 1] })
  }

  setSelected = (v) => {
    this.setState({ selectedTextBox: v })
  }

  clean_up_dependencies = () => {
    return new Promise((res, _) => {
      const step = this.props.steps[this.props.steps.length - 1]
      let redundant_deps = [];
      const dependencies = step.dependencies
      const promises = dependencies.map(dep => {
        const promise = this.is_redundant_dep(dep, dependencies, redundant_deps, step)
        return promise.then((response) => {
          if (response.trim() === 'unsat') {
            redundant_deps.push(dep)
          }
        })
      });
      Promise.all(promises).then(() => {
        step.dependencies = dependencies.filter(dep => !redundant_deps.includes(dep))
        res(step)
      })
    })
  }

  is_redundant_dep = (dependency, dependencies, redundant_deps, step) => {
    const { identifiers, relations, steps, givens, types, functions, lemmas } = this.props
    const rem_deps = dependencies.filter(dep => !redundant_deps.includes(dep) && dep !== dependency)
    let requiredSteps = validate_step_dependencies(step, rem_deps, givens, steps, lemmas)
    requiredSteps.push(step.ast)
    const promise = this.callZ3(requiredSteps, identifiers, relations, types, functions, step.i)
    return promise
  }

  updateDependenciesFromInsertionAndRemoval = (index, increment) => {
    for (let i = 0; i < this.props.steps.length; i++) {
      let dependencies = this.props.steps[i].dependencies
      let dependenciesNeedUpdating = false
      for (let j = 0; j < dependencies.length; j++) {
        if (isNaN(dependencies[j])) {
          let parts = dependencies[j].split("..")
          if (parts[0] > index + 1) {
            parts[0] = parseInt(parts[0]) + increment
            dependenciesNeedUpdating = true
          }
          if (parts[1] > index + 1) {
            parts[1] = parseInt(parts[1]) + increment
            dependenciesNeedUpdating = true
          }
          if (dependenciesNeedUpdating) {
            dependencies[j] = parts[0] + ".." + parts[1]
          }
        }
        else {
          if (dependencies[j] > index + 1) {
            dependencies[j] = parseInt(dependencies[j]) + increment
            dependenciesNeedUpdating = true
          }
        }
      }
      if (dependenciesNeedUpdating) {
        dependencies = dependencies.map(String)
        this.props.setDependency(dependencies, ['steps', i, "dependencies"])
      }
    }
  }

  updateAddLemma = () => {
    this.props.addLemmas([{ast: {}}])
  }

  render() {
    return (
      <React.Fragment>
        <div className="sidebar">
          <div className="sidebar-top">
            <img src="/iProve.png" className="logo" />
            <div className="slogan">The easiest way to construct logic proofs.</div>
          </div>
          <div className="document">
            <div className="document-title">Your proof is called</div>
            <input type="text" className="document-text" placeholder="Untitled" />
          </div>
          <div className="actions">
            <div className="actions-title">File</div>
            <div className="actions-content">
              <div className="action-button" onClick={() => {
                openDialog(PROOF_EXTENSION, ({ props, state }) => {
                  this.props.loadProof(props)
                  this.setState(state)
                })
              }}>
                <i className="fas fa-folder-open"></i>
                <div className="action-button-text">Open</div>
              </div>
              <div className="action-button" onClick={() => {
                const d = new Date()
                const date = d.getDate().toString() + (d.getMonth() + 1).toString() + d.getFullYear().toString()

                const data = { props: this.props, state: this.state }
                const name = `${date}${PROOF_EXTENSION}`

                saveDialog(data, name)
              }}>
                <i className="fas fa-save"></i>
                <div className="action-button-text">Save</div>
              </div>
              <div className="action-button" onClick={this.callLatex}>
                <i className="fas fa-print"></i>
                <div className="action-button-text">Print</div>
              </div>
              <div className="action-button" onClick={this.props.undo}>
                <i className="fas fa-undo"></i>
                <div className="action-button-text">Undo</div>
              </div>
              <div className="action-button" onClick={this.props.redo}>
                <i className="fas fa-redo"></i>
                <div className="action-button-text">Redo</div>
              </div>
            </div>
          </div>
          <div className="actions">
            <div className="actions-title">Proof</div>
            <div className="actions-content">
              <div className="action-button" onClick={this.props.clear}>
                <i className="fas fa-times"></i>
                <div className="action-button-text">Clear</div>
              </div>
              <div className="action-button" onClick={() => this.clean_up_dependencies().then(step => this.props.beautify(step))}>
                <i className="fas fa-broom"></i>
                <div className="action-button-text">Beautify</div>
              </div>
              <div className="action-button" onClick={()=>this.setState(state => ({ simple: !state.simple}))}>
                <i className="fas fa-toggle-on"></i>
                <div className="action-button-text">Switch Modes</div>
              </div>
            </div>
          </div>
          <div className="actions">
            <div className="actions-title">Lemmas</div>
            <div className="actions-content">
              <div className="action-button" onClick={() => {
                openDialog(LEMMAS_EXTENSION, ({ lemmas }) => {
                  this.props.addLemmas(lemmas)
                })
              }}>
                <i className="fas fa-file-import"></i>
                <div className="action-button-text">Import</div>
              </div>
              <div className="action-button" onClick={() => {
                const d = new Date()
                const date = d.getDate().toString() + (d.getMonth() + 1).toString() + d.getFullYear().toString()

                const data = { lemmas: this.props.lemmas }
                const name = `${date}${LEMMAS_EXTENSION}`

                saveDialog(data, name)
              }}>
                <i className="fas fa-download"></i>
                <div className="action-button-text">Export</div>
              </div>
              <div className="action-button" onClick={() => this.updateAddLemma()}>
                <i className="fas fa-plus-circle"></i>
                <div className="action-button-text">Add Lemma</div>
              </div>
            </div>
          </div>
          <div className="copyright">
            &copy; 2018 Imperial College London<br />3rd Year Group Project Group 25
          </div>
        </div>
        <div className="proof">
          { this.props.lemmas && this.props.lemmas.length !== 0 &&
            <React.Fragment>
              <div className="proof-section-container">
                <div className="proof-section">Lemmas</div>
                <div className="proof-empty"></div>
              </div>
              <TextBoxList z3={this.props.z3} start={0} steps={this.props.lemmas} type="lemmas" selectedTextBox={this.state.selectedTextBox} setSelected={this.setSelected} incrementInput={this.incrementInput} newStepAfter={this.newStepAfter} removeCurrentStep={this.removeCurrentStep} />
            </React.Fragment>
          }
          <div className="proof-section-container">
            <div className="proof-section">Givens</div>
            <div className="proof-empty"></div>
          </div>
          { this.state.simple ?
              <ProofStepList z3={this.props.z3} start={0} steps={this.props.givens} type="givens" />
            : <TextBoxList z3={this.props.z3} start={0} steps={this.props.givens} type="givens" selectedTextBox={this.state.selectedTextBox} setSelected={this.setSelected} incrementInput={this.incrementInput} newStepAfter={this.newStepAfter} removeCurrentStep={this.removeCurrentStep} />
          }
          <div className="proof-section-container">
            <div className="proof-section">Proof</div>
            <div className="proof-empty"></div>
          </div>
          { this.state.simple ?
              <ProofStepList z3={this.props.z3} steps={this.props.steps} start={this.props.givens.filter(is_step).length} showDependencies type="steps" />
            : <TextBoxList z3={this.props.z3} steps={this.props.steps} start={this.props.givens.length} showDependencies type="steps" selectedTextBox={this.state.selectedTextBox} setSelected={this.setSelected} incrementInput={this.incrementInput} newStepAfter={this.newStepAfter} removeCurrentStep={this.removeCurrentStep} />
          }
          <div className="proof-section-container">
            <div className="proof-section">Goal</div>
            <div className="proof-empty"></div>
          </div>
          { this.state.simple ?
              <ProofStepList z3={this.props.goalAchieved} steps={this.props.goal} type="goal" />
            : <TextBoxList z3={this.props.goalAchieved} steps={this.props.goal} type="goal" start={this.props.givens.length+this.props.steps.length} selectedTextBox={this.state.selectedTextBox} setSelected={this.setSelected} incrementInput={this.incrementInput} />
          }
        </div>
        { this.state.simple && <DragDrop /> }
        { this.state.simple && <Controls /> }
      </React.Fragment>
    )
  }
}

const mapDispatchToProps = dispatch => ({
  newStep: (path) => dispatch({ type: NEW_STEP, path }),
  removeStep: (path) => dispatch({ type: REMOVE_STEP, path }),
  setDependency: (list, path) => dispatch({ type: SET_STEP_DEPENDENCY, payload: list, path }),
  loadProof: (props) => dispatch({ type: LOAD_PROOF, payload: props, path: [] }),
  addLemmas: (lemmas) => dispatch({ type: ADD_LEMMAS, payload: lemmas, path: [] }),
  undo: () => dispatch(ActionCreators.undo()),
  redo: () => dispatch(ActionCreators.redo()),
  clear: () => dispatch({ type: CLEAR_PROOF, path:[] }),
  beautify: (step) => dispatch({ type: BEAUTIFY, payload: step, path:[] }),
  setZ3: (z3) => dispatch({ type: SET_Z3, payload: z3, path: [] }),
  setGoalAchieved: (ga) => dispatch({ type: SET_GOAL_ACHIEVED, payload: ga, path: [] })
})

export default connect(state => state.present, mapDispatchToProps)(IProve)