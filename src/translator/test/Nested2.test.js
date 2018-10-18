const {translate} = require('../../translator/z3')

const test_constants = ['p', 'q']
const test_rules = [{
    type: 'unary',
    symbol: 'not',
    value: {
      type: 'literal',
      value: 't'
    }
  },
  {
    type: 'binary',
    symbol: 'implies',
    lhs: {
      type: 'literal',
      value: 'p'
    },
    rhs: {
      type: 'unary',
      symbol: 'not',
      value: {
        type: 'binary',
        symbol: 'and',
        lhs: {
          type: 'literal',
          value: 'r'
        },
        rhs: {
          type: 'literal',
          value: 'q'
        }
      }
    }
  },
  {
    type: 'binary',
    symbol: 'implies',
    lhs: {
      type: 'literal',
      value: 'p'
    },
    rhs: {
      type: 'binary',
      symbol: 'or',
      lhs: {
        type: 'literal',
        value: 'r'
      },
      rhs: {
        type: 'literal',
        value: 't'
      }
    }
  },
  {
    type: 'binary',
    symbol: 'implies',
    lhs: {
      type: 'literal',
      value: 'p'
    },
    rhs: {
      type: 'unary',
      symbol: 'not',
      value: {
        type: 'literal',
        value: 'q'
      }
    }
  }]

test('Nested test 2', () => {
  expect(translate(test_rules, test_constants)).toMatchSnapshot()
})