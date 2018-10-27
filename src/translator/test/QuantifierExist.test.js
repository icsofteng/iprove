const {translate} = require('../z3')
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