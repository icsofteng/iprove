module.exports = {
  test_constants: [{type: 'literal', value: 'p'}, {type: 'literal', value: 'q'}],

  test_rules: [{
    type: 'or',
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
}