module.exports = {
  test_constants : [{type: 'literal', value: 'p'}, {type: 'literal', value: 'q'}, {type: 'literal', value: 'r'}] ,
  test_rules :[{
    type: 'and', 
    lhs: {
      type: 'and', 
      lhs: {
        type:'literal',
        value: 'p'
      }, 
      rhs: {
        type:'literal',
        value: 'q'
      }
    }, 
    rhs: {
      type: 'literal', 
      value: 'r'
    }
  }, 
  {
    type: 'literal',
    value: 'r'
  }]
}
