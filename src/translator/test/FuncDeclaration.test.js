const {translate} = require('../../translator/z3')
const {translate: translate_latex} = require('../../translator/latex')

const test_rules = [
  {
    type: 'funcDef',
    lhs: {
      type: 'literal',
      value: 'P'
    },
    rhs: {
      type: 'literal',
      value: 'Q'
    }
  },
  {
    type: 'literal',
    value: 'P'
  }
]

test('func Def test', () => {
  expect(translate(test_rules, [], [], test_constants)).toMatchSnapshot()
})
