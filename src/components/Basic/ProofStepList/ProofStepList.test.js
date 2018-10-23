import React from 'react'
import ProofStepList from './'

const ast = {type: "binary", symbol: "implies", lhs: {type:"literal", value:"p"}, rhs:  {type:"literal", value:"q"}}
const ast2 = {type: "literal", value: "p"}
const step = { dependencies: [], ast }
const step2 = { dependencies: [], ast2 }
const steps = [step, step2]
const z3State = "(unsat)";
const wrapper = shallow(<ProofStepList z3={z3State} steps={steps} />)

test('Snapshot test', () => {
  expect(wrapper).toMatchSnapshot()
})

