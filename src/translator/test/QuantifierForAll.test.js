const {translate} = require('../z3')
const {translate: translate_mathjax} = require('../mathjax')

const test_constants = ['P', 'Q']
const test_rules = [
  {
    type: 'universal_quantifier',
    symbol: 'forall',
    variable: "x",
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
  expect(translate(test_rules, [], [], test_constants)).toMatchSnapshot()
})

test('Quantifier Forall test mathjax', () => {
  expect(translate_mathjax(test_rules, [],[], test_constants)).toMatchSnapshot()
})
