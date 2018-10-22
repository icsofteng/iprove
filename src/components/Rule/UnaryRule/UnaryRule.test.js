import React from 'react'
import UnaryRule from './'

const unSymbols = {
  not: '¬'
}

test('Unary Rule empty test', () => {
  const wrapper = shallow(<UnaryRule symbols={unSymbols} path={[]}/>)
  expect(wrapper).toMatchSnapshot()
})

test('Unary Rule not test', () => {
  const wrapper = shallow(<UnaryRule symbol={'not'} symbols={unSymbols} path={[]}/>)
  expect(wrapper).toMatchSnapshot()
})