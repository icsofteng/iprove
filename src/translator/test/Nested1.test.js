const {translate} = require('../../translator/z3')
const {translate: translate_latex} = require('../../translator/latex')

const test_constants = ['P', 'Q']
const test_rules = [
  {
    type: 'binary',
    symbol: 'and',
    lhs: {
      type: 'binary',
      symbol: 'and', 
      lhs: {
        type:'literal',
        value: 'P'
      }, 
      rhs: {
        type:'literal',
        value: 'Q'
      }
    },
    rhs: {
      type: 'literal',
      value: 'P'
    },
  }
]

test('Nested test 1', () => {
  expect(translate(test_rules, [], [], test_constants, [])).toMatchSnapshot()
})


test('Nested test latex', () => {
  expect(translate_latex(test_rules, [],[], test_constants, [])).toMatchSnapshot()
})