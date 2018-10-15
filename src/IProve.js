import React, { Component } from 'react'
import Controls from './components/Controls'
import ProofSteps from './components/ProofSteps'
import DragDrop from './dragdrop'

export default class IProve extends Component {
  componentDidMount() {
    DragDrop.initialise()
  }

  render() {
    return (
      <div className="IProve">
        <Controls />
        <ProofSteps />
      </div>
    )
  }
}