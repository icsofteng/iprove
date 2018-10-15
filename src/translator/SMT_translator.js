var fs = require('fs')
var proof_file_name = 'tmp'

function translate_to_SMT(rules, constants) {
    //split goal and assumptions
    var length = rules.length
    var goal = rules.slice(length - 1)
    var assumptions = rules.slice(0, length - 1)

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

    
}

function translate_rule(rule) {
    switch(rule.type) {
        case 'and': translate_and_rule(rule); break
        case 'or': translate_or_rule(rule); break
        case 'not': translate_not_rule(rule); break
        case 'iff': translate_iff_rule(rule); break
        case 'implies': translate_implies_rule(rule); break
        default: translate_literal(rule); break
    }
}   


function translate_and_rule() {

}

function translate_or_rule() {

}

function translate_implies_rule() {

}


function translate_iff_rule(rule) {
    var expr1 = translate_rule(rule.lhs)
    var expr2 = translate_rule(rule.rhs)
    return '(iff '+ expr1 +  + expr2 + ')'
}

function translate_not_rule(rule) {
    return '( not '+ translate_rule(rule.expr) + ')'
}

function translate_literal(rule) {
    return rule.value
}
