import React from 'react'
import ProofStep from './'

const ast = { type: "binary", symbol: "implies", lhs: {type:"literal", value:"p"}, rhs:  {type:"literal", value:"q"}}
const step = { dependencies: [], ast }
const wrapper = shallow(<ProofStep step={step} index={0} showDependencies={true} offset={0} type="steps" />)

test('Snapshot test', () => {
  expect(wrapper).toMatchSnapshot()
})

