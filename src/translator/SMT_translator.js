// var test_constants1 = require('./test.js').test_constants1

var fs = require('fs')
var crypto = require('crypto')

function translate_to_SMT(rules, constants) {
    // create random file name
    var current_date = (new Date()).valueOf().toString()
    var random = Math.random().toString()
    var proof_file_name = crypto.createHash('sha1').update(current_date + random).digest('hex').toString()
    var file_contents = ""

    //split goal and assumptions
    var length = rules.length
    var goal = rules.slice(length - 1)[0]
    var assumptions = rules.slice(0, length - 1)

    // declare constants to be used in proof
    constants.forEach(element => {
        var name = element.value
        file_contents += '(declare-const ' + name + ' Bool)\n'
    });

    // translate assumptions
    assumptions.forEach(element => {
        file_contents += '(assert ' + translate_rule(element) + ')\n'
    })
    
    // translate AND NEGATE goal
    var negated_goal = '(assert (not '+ translate_rule(goal) + '))\n'
    file_contents += negated_goal
    file_contents += '(check-sat)'
    fs.writeFile(proof_file_name, file_contents, (err)=>{})
}

function translate_rule(rule) {
    switch(rule.type) {
        case 'and': return translate_and_rule(rule)
        case 'or': return translate_or_rule(rule)
        case 'not': return translate_not_rule(rule)
        case 'iff': return translate_iff_rule(rule)
        case 'implies': return translate_implies_rule(rule)
        default: return translate_literal(rule)
    }
}   

function translate_and_rule(rule) {
    lhsExpr = translate_rule(rule.lhs)
    rhsExpr = translate_rule(rule.rhs)
    return '(and ' + lhsExpr + ' ' + rhsExpr + ')'

}

function translate_or_rule(rule) {
    lhsExpr = translate_rule(rule.lhs)
    rhsExpr = translate_rule(rule.rhs)
    return '(or ' + lhsExpr + ' ' + rhsExpr + ')'
}

function translate_implies_rule(rule) {
    lhsExpr = translate_rule(rule.lhs)
    rhsExpr = translate_rule(rule.rhs)
    return '(=> ' + lhsExpr + ' ' + rhsExpr + ')'
}


function translate_iff_rule(rule) {
    var expr1 = translate_rule(rule.lhs)
    var expr2 = translate_rule(rule.rhs)
    return '(iff '+ expr1 +  + expr2 + ')'
}

function translate_not_rule(rule) {
    return '( not '+ translate_rule(rule.value) + ')'
}

function translate_literal(rule) {
    return rule.value
}

var test_constants = [{type: 'literal', value: 'p'}, {type: 'literal', value: 'q'}, {type: 'literal', value: 'r'}]
var test_rules = [{
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

//some tests
test_constants2 = [{ltype: 'literal', value: 'r'}, {ltype: 'literal', value: 'i'}, {ltype: 'literal', value: 'f'}]
test_rules2 = [
    {
        type: 'implies',
        lhs: {
            type: 'literal',
            value: 'r'
        },
        rhs: {
            type: 'not',
            value: {
                type: 'literal',
                value: 'i'
            }
        }
    },
    {
        type: 'or',
        lhs: {
            type: 'literal',
            value: 'i'
        },
        rhs: {
            type: 'literal',
            value: 'f'
        }
    },
    {
        type: 'not',
        value: {
            type: 'literal',
            value: 'f'
        }
    },
    {
        type: 'not',
        value: {
            type: 'literal',
            value: 'r'
        }
    }
]

test_constants3 = [{ltype: 'literal', value: 'a'}, {ltype: 'literal', value: 'b'},
 {ltype: 'literal', value: 'd'}, {ltype: 'literal', value: 'e'}, {ltype: 'literal', value: 'g'}]
test_rules3 = [
    {
        type: 'implies',
        lhs: {
            type: 'literal',
            value: 'a'
        },
        rhs: {
            type: 'implies',
            lhs: {
                type: 'literal',
                value: 'b'
            },
            rhs: {
                type: 'or',
                lhs: {
                    type: 'literal',
                    value: 'd'
                },
                rhs: {
                    type: 'literal',
                    value: 'e'
                }
            }
        }
    },
    {
        type: 'not',
        value: {
            type: 'or',
            lhs: {
                type: 'literal',
                value: 'd'
            },
            rhs: {
                type: 'literal',
                value: 'g'
            }
        }
    },
    {
        type: 'implies',
        lhs: {
            type: 'and',
            lhs: {
                type: 'literal',
                value: 'e'
            },
            rhs: {
                type: 'literal',
                value: 'b'
            }
        },
        rhs: {
            type: 'literal',
            value: 'g'
        }
    },
    {
        type: 'implies',
        lhs: {
            type: 'literal',
            value: 'b'
        },
        rhs: {
            type: 'not',
            value: {
                type: 'literal',
                value: 'a'
            }
        }
    }
]

translate_to_SMT(test_rules, test_constants)
translate_to_SMT(test_rules2, test_constants2)
translate_to_SMT(test_rules3, test_constants3)
