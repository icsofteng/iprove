import React from 'react'
import SymbolChooser from './'

const binSymbols = {
  and: '∧',
  or: '∨',
  implies: '⇒',
  iff: '⇔'
}


test('Symbol Chooser Empty Symbol test', () => {
  const wrapper = shallow(<SymbolChooser symbols={binSymbols}/>)
  expect(wrapper).toMatchSnapshot()
})

test('Symbol Chooser and Symbol test', () => {
  const wrapper = shallow(<SymbolChooser current={"and"} symbols={binSymbols}/>)
  expect(wrapper).toMatchSnapshot()
})

test('Symbol Chooser or Symbol test', () => {
  const wrapper = shallow(<SymbolChooser current={"or"} symbols={binSymbols}/>)
  expect(wrapper).toMatchSnapshot()
})

test('Symbol Chooser implies Symbol test', () => {
  const wrapper = shallow(<SymbolChooser current={"implies"} symbols={binSymbols}/>)
  expect(wrapper).toMatchSnapshot()
})

test('Symbol Chooser iff Symbol test', () => {
  const wrapper = shallow(<SymbolChooser current={"iff"} symbols={binSymbols}/>)
  expect(wrapper).toMatchSnapshot()
})