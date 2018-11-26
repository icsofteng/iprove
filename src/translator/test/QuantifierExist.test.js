const {translate} = require('../z3')
const {translate: translate_latex} = require('../../translator/latex')

const test_constants = [{ value: 'P', varType: 'Bool' }, { value: 'Q', varType: 'Bool' }]
const test_rules = [
  {
    type: 'existential_quantifier',
    symbol: 'exist',
    variables: [{ type: "variable", value: "x" , varType: "Type"}],
    value: {
      type: 'binary',
      symbol: 'implies',
      lhs: {
        type: 'literal',
        value: 'P'
      },
      rhs: {
        type: 'literal',
        value: 'Q'
      }
    }
  },
  {
    type: 'literal',
    value: 'P'
  }
]

test('Quantifier Exist test', () => {
  expect(translate(test_rules, test_constants, [], [], [])).toMatchSnapshot()
})

test('Qualifier Exist test latex', () => {
  expect(translate_latex(test_rules, test_constants, [], [], [])).toMatchSnapshot()
})
