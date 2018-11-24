const {translate} = require('../../translator/z3')
const {translate: translate_latex} = require('../../translator/latex')

const test_constants = [{ value: 'P', varType: 'Bool' }, { value: 'Q', varType: 'Bool' }]
const test_rules = [
  {
    type: 'binary',
    symbol: 'or',
    lhs: {
      type: 'literal',
      value: 'P'
    },
    rhs: {
      type: 'literal',
      value: 'Q'
    },
  },
  { 
    type: 'literal',
    value: 'P'
  }
]

test('Or test', () => {
  expect(translate(test_rules, test_constants, [], [])).toMatchSnapshot()
})

test('Or test latex', () => {
  expect(translate_latex(test_rules, test_constants, [], [])).toMatchSnapshot()
})