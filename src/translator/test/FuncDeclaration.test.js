const {translate} = require('../../translator/z3')
const {translate: translate_latex} = require('../../translator/latex')

const test_constants = ['P']
const test_rules = [
  {
    type: 'funcDef',
    name: 'friends',
    params: [{type: 'type', value: 'Person'}, {type: 'type', value: 'Person'}],
    returnType: {type:'type', value: 'Bool'}
  },
  {
    type: 'literal',
    value: 'P'
  }
]

test('func Def test', () => {
  expect(translate(test_rules, [], [], test_constants, ['Person'])).toMatchSnapshot()
})

const test_constants2 = ['P']
const test_rules2 = [
  {
    type:'funcDef',
    name:'Power',
    params:[{type: 'type', value: 'Dragon'}, {type: 'type', value: 'Dragon'}],
    returnType: {type:'type', value: 'Int'}
  },
  {
    type: 'literal',
    value: 'P'
  }
]
test('func Def Dragon test', () => {
  expect(translate(test_rules2, [], [], test_constants2, ['Dragon'])).toMatchSnapshot()
})

const test_constants3 = ['P']
const test_rules3 = [
  {
    type:'funcDef',
    name:'Happy',
    params:[{type: 'type', value: 'Dragon'}, {type: 'type', value: 'Human'}],
    returnType: {type:'type', value: 'Reward'}
  },
  {
    type: 'literal',
    value: 'P'
  }
]
test('func Def Happy test', () => {
  expect(translate(test_rules3, [], [], test_constants3, ['Reward' ,'Dragon', 'Human'])).toMatchSnapshot()
})

