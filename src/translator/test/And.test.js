const {translate: translate_z3} = require('../../translator/z3')
const {translate: translate_mathjax} = require('../../translator/mathjax')

const test_constants = ['P', 'Q']
const test_rules = [
  {
    type: 'binary',
    symbol: 'and',
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

test('And test z3', () => {
  expect(translate_z3(test_rules, [],[], test_constants)).toMatchSnapshot()
})

test('And test mathjax', () => {
  expect(translate_mathjax(test_rules, [],[], test_constants)).toMatchSnapshot()
})