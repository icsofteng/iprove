import React from 'react'
import ProofStepList from './'

const rule = {type: "binary", symbol: "implies", lhs: {type:"literal", value:"p"}, rhs:  {type:"literal", value:"q"}}
const rule2 = {type: "literal", value: "p"}
const steps = [rule, rule2]
const z3State = "(unsat)";
const wrapper = shallow(<ProofStepList z3={z3State} steps={steps} />)

test('Snapshot test', () => {
  expect(wrapper).toMatchSnapshot()
})

