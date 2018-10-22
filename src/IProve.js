import React, { Component } from 'react'
import Controls from './components/Controls'
import ProofStepList from './components/ProofStepList'
import DragDrop from './components/DragDrop'
import TextBoxList from './components/TextBoxList'
import { connect } from 'react-redux';

class IProve extends Component {
  constructor(props) {
    super(props)
    this.state = { z3: "", simple: false }
  }
  componentDidUpdate(prevProps) {
    if (prevProps.steps !== this.props.steps) {
      const { steps: rules, constants } = this.props
      fetch('/z3', {
        method: "POST",
        headers: {"Content-Type": "application/json; charset=utf-8"},
        body: JSON.stringify({rules, constants})
      }).then(r => r.text()).then(response => {
        this.setState({ z3: response.replace(/(\r\n\t|\n|\r\t)/gm,"") })
      })
    }
  }

  render() {
    return (
      this.state.simple ?
      <div className="IProve">
        <DragDrop />
        <Controls />
        <ProofStepList z3={this.state.z3} steps={this.props.steps} />
      </div>
      :
      <div className="IProve">
        <TextBoxList steps={this.props.steps} />
      </div>
    )
  }
}

export default connect(state => state)(IProve)