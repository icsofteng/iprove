import React from 'react'
import FalseRule from './'

test('False Rule test', () => {
  const wrapper = shallow(<FalseRule />)
  expect(wrapper).toMatchSnapshot()
})