import React, { Component } from 'react'
import { connect } from 'react-redux'
import _ from 'underscore'
import Controls from './Basic/Controls'
import ProofStepList from './Basic/ProofStepList'
import DragDrop from './Basic/DragDrop'
import TextBoxList from './Advanced/TextBoxList'
import { NEW_STEP, LOAD_PROOF, REMOVE_STEP, CLEAR_PROOF, BEAUTIFY, SET_STEP_DEPENDENCY } from '../constants'
import { is_step, validate_step_dependencies } from '../utils'
import Toolbar from './Shared/Toolbar'
import { saveDialog, openDialog } from './Shared/Toolbar/actions'
import { ActionCreators } from 'redux-undo'
import styles from './styles.scss'
import ModalLemmas from './Shared/ModalLemmas';

class IProve extends Component {
  constructor(props) {
    super(props)
    this.state = {
      goalAchieved: [],
      z3: [],
      simple: false,
      selectedTextBox: ["givens", 0],
      viewAddLemmas: false
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
        const currentZ3 = this.state.z3
        currentZ3[i] = response.trim()
        this.setState({ z3: currentZ3 }, () => {
          // Check goal
          if (_.isEqual(this.props.goal[0].ast, this.props.steps[this.props.steps.length - 1].ast)) {
            this.setState({ goalAchieved: [currentZ3[currentZ3.length - 1]] }, () => resolve())
          }
          else {
            resolve()
          }
        })
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
    const { identifiers, relations, steps, givens, types, functions } = this.props
    this.setState({ goalAchieved: [] })
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
          else {
            dependenciesNoRanges.push(parseInt(d))
          }
        })
        let requiredSteps = validate_step_dependencies(step, dependenciesNoRanges, givens, steps)
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
    const { identifiers, relations, steps, givens, types, functions } = this.props
    const rem_deps = dependencies.filter(dep => !redundant_deps.includes(dep) && dep !== dependency)
    let requiredSteps = validate_step_dependencies(step, rem_deps, givens, steps)
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

  updateViewAddLemmas = () => {
    this.setState(state => ({ viewAddLemmas: !state.viewAddLemmas }))
  }



  render() {
    return (
      <div className={styles.iprove}>
        { this.state.viewAddLemmas && <ModalLemmas onCancel={()=>this.updateViewAddLemmas()} z3={this.state.z3}/>  }
        <Toolbar
          simple={this.state.simple}
          onSave={()=>saveDialog(this.props, this.state)}
          onOpen={()=>openDialog((p, s)=>{this.props.loadProof(p); this.setState(s)})}
          onSwitch={()=>this.setState(state => ({ simple: !state.simple}))}
          onUndo={this.props.undo}
          onRedo={this.props.redo}
          onClear={this.props.clear}
          onBeautify={() => this.clean_up_dependencies().then(step => this.props.beautify(step))}
          onExportPdf={this.callLatex}
          onAddLemma={() => this.updateViewAddLemmas()}
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
                    : <TextBoxList z3={this.state.z3} start={0} steps={this.props.givens} type="givens" selectedTextBox={this.state.selectedTextBox} setSelected={this.setSelected} incrementInput={this.incrementInput} newStepAfter={this.newStepAfter} removeCurrentStep={this.removeCurrentStep} />
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
                    : <TextBoxList z3={this.state.z3} steps={this.props.steps} start={this.props.givens.length} showDependencies type="steps" selectedTextBox={this.state.selectedTextBox} setSelected={this.setSelected} incrementInput={this.incrementInput} newStepAfter={this.newStepAfter} removeCurrentStep={this.removeCurrentStep} />
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
  removeStep: (path) => dispatch({ type: REMOVE_STEP, path }),
  setDependency: (list, path) => dispatch({ type: SET_STEP_DEPENDENCY, payload: list, path }),
  loadProof: (props) => dispatch({ type: LOAD_PROOF, payload: props, path: [] }),
  undo: () => dispatch(ActionCreators.undo()),
  redo: () => dispatch(ActionCreators.redo()),
  clear: () => dispatch({ type: CLEAR_PROOF, path:[] }),
  beautify: (step) => dispatch({ type: BEAUTIFY, payload: step, path:[] }),
})

export default connect(state => state.present, mapDispatchToProps)(IProve)
