const {translate} = require('../../translator/z3')
const {translate: translate_mathjax} = require('../../translator/mathjax')

const test_constants = ['p']
const test_rules = [{
  type: 'unary',
  symbol: 'not',
  value: {
    type: 'literal',
    value: 'p'
  }
}]


test('Not test', () => {
  expect(translate(test_rules, test_constants, [])).toMatchSnapshot()
})

test('Not test mathjax', () => {
  expect(translate_mathjax(test_rules, test_constants,[])).toMatchSnapshot()
})