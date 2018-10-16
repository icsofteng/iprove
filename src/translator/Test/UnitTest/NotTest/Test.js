module.exports = {
  test_constants: [{type: 'literal', value: 'p'}],

  test_rules: [{
    type: 'not',
    value: {
      type: 'literal',
      value: 'p'
    }
  },
  {
    type: 'literal',
    value: 'p'
  }]
}