import React from 'react'
import LiteralRule from '.'


test('Literal undefined test', () => {
  const wrapper = shallow(<LiteralRule type={'literal'} path={[]}/>)
  expect(wrapper).toMatchSnapshot()
})

test('Literal p test', () => {
  const wrapper = shallow(<LiteralRule type={'literal'} value={'p'} path={[]}/>)
  expect(wrapper).toMatchSnapshot()
})