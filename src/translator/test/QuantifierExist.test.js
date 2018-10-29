const {translate} = require('../z3')
const {translate: translate_mathjax} = require('../../translator/mathjax')

const test_constants = ['p']
const test_rules = [
  {
    type: 'quantifier',
    symbol: 'exist',
    variable: "x", 
    value: { 
      type: 'binary',
      symbol: 'implies',
      lhs: {
        type: 'literal',
        value: 'x'
      },
      rhs: {
        type: 'literal',
        value: 'p'
      }
    }
  },
  {
    type: 'literal',
    value: 'p'
  }  
]

test('Quantifier Exist test', () => {
  expect(translate(test_rules, test_constants, [])).toMatchSnapshot()
})

test('Qualifier Exist test mathjax', () => {
  expect(translate_mathjax(test_rules, test_constants,[])).toMatchSnapshot()
})