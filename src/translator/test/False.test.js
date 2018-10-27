const {translate} = require('../../translator/z3')

const test_constants = ['p']
const test_rules = [
 {
    type: 'binary',
    symbol: 'or',
    lhs: {
      type: 'literal',
      value: 'p'
    },
    rhs: {
      type: 'false'
    },
  },
  {
    type: 'literal',
    value: 'p'
  }
]


test('False test', () => {
  expect(translate(test_rules, test_constants, [])).toMatchSnapshot()
})