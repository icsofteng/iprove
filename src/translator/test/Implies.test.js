const {translate} = require('../../translator/z3')

const test_constants = ['p', 'q']
const test_rules = [{
  type: 'binary',
  symbol: 'implies',
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


test('Implies test', () => {
  expect(translate(test_rules, test_constants)).toMatchSnapshot()
})