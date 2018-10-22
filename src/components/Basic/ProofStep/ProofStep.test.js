import React from 'react'
import ProofStep from './'

const rule = { type: "binary", symbol: "implies", lhs: {type:"literal", value:"p"}, rhs:  {type:"literal", value:"q"}}
const wrapper = shallow(<ProofStep rule={rule} index={0} />)

test('Snapshot test', () => {
  expect(wrapper).toMatchSnapshot()
})

