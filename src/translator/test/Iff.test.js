const {translate} = require('../../translator/z3')

const test_constants = ['p', 'q']
const test_rules = [
  {
    dependencies: [],
    ast: {
      type: 'binary',
      symbol: 'iff',
      lhs: {
        type: 'literal',
        value: 'p'
      },
      rhs: {
        type: 'literal',
        value: 'q'
      },
    }
  }
]

test('Iff test', () => {
  expect(translate(test_rules, test_constants)).toMatchSnapshot()
})