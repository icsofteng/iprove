const {translate} = require('../../translator/z3')

const test_constants = ['p', 'q']
const test_rules = [
  {
    dependencies: [],
    ast: {
      type: 'binary',
      symbol: 'and',
      lhs: {
        type: 'binary',
        symbol: 'and', 
        lhs: {
          type:'literal',
          value: 'p'
        }, 
        rhs: {
          type:'literal',
          value: 'q'
        }
      },
      rhs: {
        type: 'literal',
        value: 'q'
      },
    }
  }
]

test('Nested test 1', () => {
  expect(translate(test_rules, test_constants, [])).toMatchSnapshot()
})