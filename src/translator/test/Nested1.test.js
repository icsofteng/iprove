const {translate} = require('../../translator/z3')
const {translate: translate_mathjax} = require('../../translator/mathjax')

const test_constants = ['p', 'q']
const test_rules = [
  {
    type: 'binary',
    symbol: 'and',
    lhs: {
      type: 'binary',
      symbol: 'and', 
      lhs: {
        type:'literal',
        value: 'p'
      }, 
      rhs: {
        type:'literal',
        value: 'q'
      }
    },
    rhs: {
      type: 'literal',
      value: 'q'
    },
  }
]

test('Nested test 1', () => {
  expect(translate(test_rules, test_constants, [])).toMatchSnapshot()
})


test('Nested test mathjax', () => {
  expect(translate_mathjax(test_rules, test_constants,[])).toMatchSnapshot()
})