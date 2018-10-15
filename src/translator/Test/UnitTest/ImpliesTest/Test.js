var test_constants = [{type: 'literal', value: 'p'}, {type: 'literal', value: 'q'}]

var test_rules = [{
    type: 'implies',
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