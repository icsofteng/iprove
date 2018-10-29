const {translate} = require('../../translator/z3')
const {translate: translate_mathjax} = require('../../translator/mathjax')

const test_constants = ['p', 'q']
const test_rules = [
  {
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

test('Nested 2 test', () => {
  expect(translate(test_rules, test_constants, [])).toMatchSnapshot()
})


test('Nested 2 test mathjax', () => {
  expect(translate_mathjax(test_rules, test_constants,[])).toMatchSnapshot()
})