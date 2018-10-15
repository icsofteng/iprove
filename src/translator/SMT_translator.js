var fs = require('fs')
var proof_file_name = 'tmp'

function translate_to_SMT(rules, constants) {
    //split goal and assumptions
    var length = rules.length
    var goal = rules.slice(length - 1)[0]
    console.log(goal)
    var assumptions = rules.slice(0, length - 1)
    console.log(assumptions)


    // declare constants to be used in proof
    constants.forEach(element => {
        var name = element.value
        var var_declaration = '(declare-const ' + name + ' Bool)\n'
        fs.appendFile(proof_file_name,var_declaration,(err) =>{})
    });

    // translate assumptions
    assumptions.forEach(element => {
        var rule_declaration = '(assert ' + translate_rule(element) + ')'
        fs.appendFile(proof_file_name, rule_declaration,() =>{})
    })
    
    // translate AND NEGATE goal
    var negated_goal = '(assert (not '+ translate_rule(goal) + '))\n'
    fs.appendFile(proof_file_name, negated_goal, () =>{})
    fs.appendFile(proof_file_name, '(check-sat)', () =>{})

    
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
    rule = '(and ' + lhsExpr + ' ' + rhsExpr + ')'
    
    return rule
}

function translate_or_rule() {
    lhsExpr = translate_rule(rule.lhs)
    rhsExpr = translate_rule(rule.rhs)
    rule = '(or ' + lhsExpr + ' ' + rhsExpr + ')'
    
    return rule
}

function translate_implies_rule() {
    lhsExpr = translate_rule(rule.lhs)
    rhsExpr = translate_rule(rule.rhs)
    rule = '(=> ' + lhsExpr + ' ' + rhsExpr + ')'
    
    return rule
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

translate_to_SMT(test_rules, test_constants)
