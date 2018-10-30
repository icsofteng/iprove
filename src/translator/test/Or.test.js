const {translate} = require('../../translator/z3')
const {translate: translate_mathjax} = require('../../translator/mathjax')

const test_constants = ['P', 'Q']
const test_rules = [
  {
    type: 'binary',
    symbol: 'or',
    lhs: {
      type: 'literal',
      value: 'P'
    },
    rhs: {
      type: 'literal',
      value: 'Q'
    },
  },
  { 
    type: 'literal',
    value: 'P'
  }
]

test('Or test', () => {
  expect(translate(test_rules, [], [], test_constants)).toMatchSnapshot()
})

test('Or test mathjax', () => {
  expect(translate_mathjax(test_rules, [],[], test_constants)).toMatchSnapshot()
})