const {translate} = require('../../translator/z3')
const {translate: translate_latex} = require('../../translator/latex')

const test_constants = ['P']
const test_rules = [
 {
    type: 'binary',
    symbol: 'or',
    lhs: {
      type: 'literal',
      value: 'P'
    },
    rhs: {
      type: 'false'
    },
  },
  {
    type: 'literal',
    value: 'P'
  }
]


test('False test', () => {
  expect(translate(test_rules, [], [], test_constants)).toMatchSnapshot()
})

test('False test latex', () => {
  expect(translate_latex(test_rules, [],[], test_constants)).toMatchSnapshot()
})