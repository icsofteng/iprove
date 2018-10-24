const {translate} = require('../../translator/z3')

const test_constants = ['p']
const test_rules = [
  {
    dependencies: [],
    ast: {
      type: 'function-def',
      name: 'F',
      inputTypes: [
        {
          type: 'varType',
          value: 'Int'
        },
        {
          type: 'varType',
          value: 'Int'
        }
      ],
      outputType: {
        type: 'varType',
        value: 'Int'
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

test('Function Def test', () => {
  expect(translate(test_rules, test_constants, [])).toMatchSnapshot()
})