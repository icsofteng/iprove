import React, { Component } from 'react'
import Controls from './components/Controls'
import ProofSteps from './components/ProofSteps'
import DragDrop from './components/DragDrop'
import { connect } from 'react-redux';

class IProve extends Component {
  componentDidUpdate() {
    const { steps: rules, constants } = this.props
    fetch('/z3', {
      method: "POST",
      headers: {"Content-Type": "application/json; charset=utf-8"},
      body: JSON.stringify({rules, constants})
    }).then(response => {
      console.log(response)
    })
  }

  render() {
    return (
      <div className="IProve">
        <DragDrop />
        <Controls />
        <ProofSteps steps={this.props.steps} />
      </div>
    )
  }
}

export default connect(state => state)(IProve)