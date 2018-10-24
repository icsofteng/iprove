const {translate} = require('../../translator/z3')

const test_constants = ['p']
const test_rules = [{
  dependencies: [],
  ast: {
    type: 'binary',
    symbol: 'implies',
    lhs: {
      type: 'literal',
      value: 'p'
    },
    rhs: {
      type: 'true'
    }
  }
}]


test('True test', () => {
  expect(translate(test_rules, test_constants, [])).toMatchSnapshot()
})