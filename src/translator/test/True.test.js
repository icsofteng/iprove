const {translate} = require('../../translator/z3')
const {translate: translate_mathjax} = require('../../translator/mathjax')

const test_constants = ['p']
const test_rules = [{
  type: 'binary',
  symbol: 'implies',
  lhs: {
    type: 'literal',
    value: 'p'
  },
  rhs: {
    type: 'true'
  }
}]


test('True test', () => {
  expect(translate(test_rules, test_constants, [])).toMatchSnapshot()
})

test('True test mathjax', () => {
  expect(translate_mathjax(test_rules, test_constants,[])).toMatchSnapshot()
})