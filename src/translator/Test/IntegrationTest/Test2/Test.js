
var test_constants = [{type: 'literal', value: 't'}, {type: 'literal', value: 'p'}, {type: 'literal', value: 'r'}, {type: 'literal', value: 'q'}]
var test_rules = [{
    type: 'not',
    value: 't'
},
{
    type: 'implies',
    lhs: {
        type: 'literal',
        value: 'p'
    },
    rhs: {
        type: 'not',
        value: {
            type: 'and',
            lhs: {
                type: 'literal',
                value: 'r'
            },
            rhs: {
                type: 'literal',
                value: 'q'
            }
        }
    }

},
{
    type: 'implies',
    lhs: {
        type: 'literal',
        value: 'p'
    },
    rhs: {
        type: 'or',
        lhs: {
            type: 'literal',
            value: 'r'
        },
        rhs: {
            type: 'literal',
            value: 't'
        }
    }
},
{
    type: 'implies',
    lhs: {
        type: 'literal',
        value: 'p'
    },
    rhs: {
        type: 'not',
        value: {
            type: 'literal',
            value: 'q'
        }
    }
}]