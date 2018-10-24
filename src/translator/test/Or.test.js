const {translate} = require('../../translator/z3')

const test_constants = ['p', 'q']
const test_rules = [
  {
    dependencies: [],
    ast: {
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
    }
  },
  {
    dependencies: [], 
    ast: { 
      type: 'literal',
      value: 'p'
    }
  }
]


test('Or test', () => {
  expect(translate(test_rules, test_constants, [])).toMatchSnapshot()
})