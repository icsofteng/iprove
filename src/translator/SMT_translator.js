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

    })
    
    // translate AND NEGATE goal

    
}

function translate_rule() {
    


}   

function translate_and_rule() {

}

function translate_or_rule() {

}

function translate_implies_rule() {

}

function translate_iff_rule() {

}

function translate_not_rule() {

}

function translate_literal() {

}
