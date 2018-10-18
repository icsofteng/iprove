import React from 'react'
import BinaryRule from './'

const p = {type:'literal', value: 'p'}
const q = {type:'literal', value: 'q'}
const binary = {type:'binary'}


test('p implies q test', () => {
  const wrapper = shallow(<BinaryRule lhs={p} symbol={'implies'} rhs={q} path={[]}/>)
  expect(wrapper).toMatchSnapshot()
})


test('p implies nothing test', () => {
  const wrapper = shallow(<BinaryRule lhs={p} symbol={'implies'} rhs={undefined} path={[]}/>)
  expect(wrapper).toMatchSnapshot()
})

test('nothing implies p test', () => {
  const wrapper = shallow(<BinaryRule symbol={'implies'} rhs={p} path={[]}/>)
  expect(wrapper).toMatchSnapshot()
})

test('nothing implies nothing', () => {
  const wrapper = shallow(<BinaryRule symbol={'implies'} path={[]}/>)
  expect(wrapper).toMatchSnapshot()
})

test('p and q test', () => {
  const wrapper = shallow(<BinaryRule lhs={p} rhs={q} symbol={'and'} path={[]}/>)
  expect(wrapper).toMatchSnapshot()
})

test('p and binary operator test', () => {
  const wrapper = shallow(<BinaryRule lhs={p} rhs={binary} symbol={'and'} path={[]}/>)
  expect(wrapper).toMatchSnapshot()
})

test('binary operator and q test', () => {
  const wrapper = shallow(<BinaryRule lhs={binary} rhs={q} symbol={'and'} path={[]}/>)
  expect(wrapper).toMatchSnapshot()
})

