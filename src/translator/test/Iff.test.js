const {translate} = require('../../translator/z3')
const {translate: translate_latex} = require('../../translator/latex')

const test_constants = [{ value: 'P', varType: 'Bool' }, { value: 'Q', varType: 'Bool' }]
const test_rules = [
  {
    type: 'binary',
    symbol: 'iff',
    lhs: {
      type: 'literal',
      value: 'P'
    },
    rhs: {
      type: 'literal',
      value: 'Q'
    }
  },
  {
    type: 'literal',
    value: 'P'
  }
]

test('Iff test', () => {
  expect(translate(test_rules, test_constants, [], [])).toMatchSnapshot()
})

test('Iff test latex', () => {
  expect(translate_latex(test_rules,test_constants, [], [])).toMatchSnapshot()
})