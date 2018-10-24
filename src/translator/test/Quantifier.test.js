const {translate} = require('../z3')
const test_constants = ['x', 'p']

const test_rules = [
  {
    dependencies: [],
    ast: {
      type: 'quantifier',
      symbol: 'forall',
      variable: {
        value:"x",
        varType: {
          value: 'Int'
        }
      },
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

test('Quantifier test', () => {
  // expect(translate(test_rules, test_constants)).toMatchSnapshot()
})