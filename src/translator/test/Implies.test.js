const {translate} = require('../../translator/z3')
const {translate: translate_mathjax} = require('../../translator/mathjax')

const test_constants = ['P', 'Q']
const test_rules = [
  {
    type: 'binary',
    symbol: 'implies',
    lhs: {
      type: 'literal',
      value: 'P'
    },
    rhs: {
      type: 'literal',
      value: 'Q'
    }
  }
]

test('Implies test', () => {
  expect(translate(test_rules, [], [], test_constants)).toMatchSnapshot()
})


test('Implies test mathjax', () => {
  expect(translate_mathjax(test_rules, [],[], test_constants)).toMatchSnapshot()
})