const {translate} = require('../../translator/z3')

const test_constants = ['p', 'q']
const test_steps = [
  {
    dependencies: [],
    ast: {
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
      }
  },
  {
  dependencies: [],
    ast: {
        type: 'literal',
        value: 'p'
      }
  }
]

test('Iff test', () => {
  expect(translate(test_steps, test_constants, [])).toMatchSnapshot()
})