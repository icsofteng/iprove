import React from 'react'
import Controls from './'

const wrapper = shallow(<Controls />)

test('Snapshot test', () => {
  expect(wrapper).toMatchSnapshot()
})

