const {translate} = require('../../translator/z3')
const {translate: translate_mathjax} = require('../../translator/mathjax')

const test_constants = ['p', 'q']
const test_rules = [
  {
    type: 'binary',
    symbol: 'or',
    lhs: {
      type: 'literal',
      value: 'p'
    },
    rhs: {
      type: 'literal',
      value: 'q'
    },
  },
  { 
    type: 'literal',
    value: 'p'
  }
]

test('Or test', () => {
  expect(translate(test_rules, test_constants, [])).toMatchSnapshot()
})

test('Or test mathjax', () => {
  expect(translate_mathjax(test_rules, test_constants,[])).toMatchSnapshot()
})