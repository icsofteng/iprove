import React, { Component } from 'react'
import Controls from './components/Controls'
import ProofSteps from './components/ProofSteps'

export default class IProve extends Component {
  render() {
    return (
      <div className="IProve">
        <Controls />
        <ProofSteps />
      </div>
    )
  }
}