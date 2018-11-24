const {translate} = require('../z3')
const {translate: translate_latex} = require('../latex')

const test_constants = [{ value: 'P', varType: 'Bool' }, { value: 'Q', varType: 'Bool' }]
const test_rules = [
  {
    type: 'universal_quantifier',
    symbol: 'forall',
    variables: [{ type: "variable", value: "x" , varType:'Type'}],
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
  }
]

test('Quantifier Forall test', () => {
  expect(translate(test_rules, test_constants, [], [])).toMatchSnapshot()
})

test('Quantifier Forall test latex', () => {
  expect(translate_latex(test_rules, test_constants, [], [])).toMatchSnapshot()
})
