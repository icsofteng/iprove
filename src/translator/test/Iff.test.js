const {translate} = require('../../translator/z3')

const test_constants = ['p', 'q']
const test_steps = [
  {
    type: 'binary',
    symbol: 'iff',
    lhs: {
      type: 'literal',
      value: 'p'
    },
    rhs: {
      type: 'literal',
      value: 'q'
    }
  },
  {
    type: 'literal',
    value: 'p'
  }
]

test('Iff test', () => {
  expect(translate(test_steps, test_constants, [])).toMatchSnapshot()
})