const {translate} = require('../z3')
const test_constants = ['p']
const relations = []
const test_rules = [
  {
    dependencies: [],
    ast: {
      type: 'quantifier',
      symbol: 'forall',
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
    }
  }
]

test('Quantifier Forall test', () => {
  expect(translate(test_rules, test_constants, [])).toMatchSnapshot()
})