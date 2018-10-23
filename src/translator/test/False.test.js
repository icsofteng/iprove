const {translate} = require('../../translator/z3')

const test_constants = ['p']
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
        type: 'false'
      },
    }
  }
]


test('False test', () => {
  expect(translate(test_rules, test_constants)).toMatchSnapshot()
})