import React from 'react'
import Rule from '../'
import SymbolChooser from '../SymbolChooser'
import RulePlaceholder from '../../RulePlaceholder'
import ProofStepList from '../../ProofStepList'
import ProofStep from '../../ProofStepList'
import { is_step } from '../../../../utils'


const OrRule = (props) =>
  <React.Fragment>
    <ProofStepList z3={[]} steps={[]} start={3} showDependencies type="steps" />
    <ProofStepList z3={[]} steps={[]} start={4} showDependencies type="steps" />
    

  </React.Fragment>

export default OrRule
