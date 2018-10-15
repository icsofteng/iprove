import React, { Component } from 'react'
import Controls from './components/Controls'
import ProofSteps from './components/ProofSteps'
import DragDrop from './components/DragDrop'

export default class IProve extends Component {
  render() {
    return (
      <div className="IProve">
        <DragDrop />
        <Controls />
        <ProofSteps />
      </div>
    )
  }
}