import React from 'react'
import TrueRule from './'

test('False Rule test', () => {
  const wrapper = shallow(<TrueRule />)
  expect(wrapper).toMatchSnapshot()
})