const {translate} = require('../../translator/z3')
const {translate: translate_mathjax} = require('../../translator/mathjax')

const test_constants = ['p', 'q']
const test_rules = [
  {
    type: 'binary',
    symbol: 'iff',
    lhs: {
      type: 'literal',
      value: 'p'
    },
    rhs: {
      type: 'literal',
      value: 'q'
    }
  },
  {
    type: 'literal',
    value: 'p'
  }
]

test('Iff test', () => {
  expect(translate(test_rules, test_constants, [])).toMatchSnapshot()
})

test('Iff test mathjax', () => {
  expect(translate_mathjax(test_rules, test_constants,[])).toMatchSnapshot()
})