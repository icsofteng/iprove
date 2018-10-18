const {translate} = require('../../translator/z3')

const test_constants = ['p']
const test_rules = [{
  type: 'unary',
  symbol: 'not',
  value: {
    type: 'literal',
    value: 'p'
  }
},
{
  type: 'literal',
  value: 'p'
}]


test('Not test', () => {
  expect(translate(test_rules, test_constants)).toMatchSnapshot()
})