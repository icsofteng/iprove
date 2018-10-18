const {translate} = require('../../translator/z3')

const test_constants = ['p', 'q']
const test_rules = [{
  type: 'binary',
  symbol: 'or',
  lhs: {
    type: 'literal',
    value: 'p'
  },
  rhs: {
    type: 'literal',
    value: 'q'
  },
},
{
  type: 'literal',
  value: 'p'
}]


test('Or test', () => {
  expect(translate(test_rules, test_constants)).toMatchSnapshot()
})