const {translate: translate_z3} = require('../../translator/z3')
const {translate: translate_latex} = require('../../translator/latex')

const test_constants = [{ value: 'P', varType: 'Bool' }, { value: 'Q', varType: 'Bool' }]
const test_rules = [
  {
    type: 'binary',
    symbol: 'and',
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

test('And test z3', () => {
  expect(translate_z3(test_rules, test_constants, [], [], [])).toMatchSnapshot()
})

test('And test latex', () => {
  expect(translate_latex(test_rules, test_constants, [], [], [])).toMatchSnapshot()
})