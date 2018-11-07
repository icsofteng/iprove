const {translate} = require('../../translator/z3')
const {translate: translate_latex} = require('../../translator/latex')

const test_constants = ['P', 'Q', 'R', 'T']
const test_rules = [
  {
    type: 'unary',
    symbol: 'not',
    value: {
      type: 'literal',
      value: 'T'
    }
  },
  {
    type: 'binary',
    symbol: 'implies',
    lhs: {
      type: 'literal',
      value: 'P'
    },
    rhs: {
      type: 'unary',
      symbol: 'not',
      value: {
        type: 'binary',
        symbol: 'and',
        lhs: {
          type: 'literal',
          value: 'R'
        },
        rhs: {
          type: 'literal',
          value: 'Q'
        }
      }
    }
  },
  {
    type: 'binary',
    symbol: 'implies',
    lhs: {
      type: 'literal',
      value: 'P'
    },
    rhs: {
      type: 'binary',
      symbol: 'or',
      lhs: {
        type: 'literal',
        value: 'R'
      },
      rhs: {
        type: 'literal',
        value: 'T'
      }
    }
  },
  {
    type: 'binary',
    symbol: 'implies',
    lhs: {
      type: 'literal',
      value: 'P'
    },
    rhs: {
      type: 'unary',
      symbol: 'not',
      value: {
        type: 'literal',
        value: 'Q'
      }
    }
  }]

test('Nested 2 test', () => {
  expect(translate(test_rules, [], [], test_constants, [])).toMatchSnapshot()
})


test('Nested 2 test latex', () => {
  expect(translate_latex(test_rules, [],[], test_constants, [])).toMatchSnapshot()
})