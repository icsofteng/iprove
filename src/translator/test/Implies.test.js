const {translate} = require('../../translator/z3')
const {translate: translate_mathjax} = require('../../translator/mathjax')

const test_constants = ['p', 'q']
const test_rules = [
  {
    type: 'binary',
    symbol: 'implies',
    lhs: {
      type: 'literal',
      value: 'p'
    },
    rhs: {
      type: 'literal',
      value: 'q'
    }
  }
]

test('Implies test', () => {
  expect(translate(test_rules, test_constants, [])).toMatchSnapshot()
})


test('Implies test mathjax', () => {
  expect(translate_mathjax(test_rules, test_constants,[])).toMatchSnapshot()
})