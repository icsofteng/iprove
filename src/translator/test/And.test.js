const {translate} = require('../../translator/z3')

const test_constants = ['p', 'q']
const test_rules = [
  {
    dependencies: [],
    ast: {
      type: 'binary',
      symbol: 'and',
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

test('And test', () => {
  expect(translate(test_rules, test_constants,[])).toMatchSnapshot()
})