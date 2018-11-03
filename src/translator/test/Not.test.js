const {translate} = require('../../translator/z3')
const {translate: translate_latex} = require('../../translator/latex')

const test_constants = ['P']
const test_rules = [{
  type: 'unary',
  symbol: 'not',
  value: {
    type: 'literal',
    value: 'P'
  }
}]


test('Not test', () => {
  expect(translate(test_rules, [], [], test_constants)).toMatchSnapshot()
})

test('Not test latex', () => {
  expect(translate_latex(test_rules, [],[], test_constants)).toMatchSnapshot()
})