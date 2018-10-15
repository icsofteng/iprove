const translate_to_SMT = require('./SMT_translator.js').translate_to_SMT;
var fs = require('fs')
var proof_file_name = 'tmp'

var test_constants1 = [{type: 'literal', value: 'p'}, {type: 'literal', value: 'q'}, {type: 'literal', value: 'r'}]
var test_rules1 = [{
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

var test_constants2 = [{type: 'literal', value: 't'}, {type: 'literal', value: 'p'}, {type: 'literal', value: 'r'}, {type: 'literal', value: 'q'}]
var test_rule2 = [{
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
            value: 'T'
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

// test('adds 1 + 2 to equal 3', () => {
//     expect(sum(1, 2)).toBe(3);
//   });

function compareFile(tmp, testFile) {
    
}
e
test('Translator test', () => {
    translate_to_SMT(test_constants1, test_rules1)
    expect(compareFile).toBe();
  });
readtmp()