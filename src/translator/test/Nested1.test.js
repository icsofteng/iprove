const {translate} = require('../../translator/z3')
const {translate: translate_mathjax} = require('../../translator/mathjax')

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
  expect(translate(test_rules, [], [], test_constants)).toMatchSnapshot()
})


test('Nested test mathjax', () => {
  expect(translate_mathjax(test_rules, [],[], test_constants)).toMatchSnapshot()
})