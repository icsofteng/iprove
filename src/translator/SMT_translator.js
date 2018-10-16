// const test_constants1 = require('./test.js').test_constants1

const fs = require('fs')
const crypto = require('crypto')

function translate_to_SMT(rules, constants, path = undefined) {
  // create random file name
  let proof_file_name;
  let file_contents = ""

  if (path) {
    proof_file_name = path
  } else {
    const current_date = (new Date()).valueOf().toString()
    const random = Math.random().toString()
    proof_file_name = crypto.createHash('sha1').update(current_date + random).digest('hex').toString()
  }

  //split goal and assumptions
  const length = rules.length
  const goal = rules.slice(length - 1)[0]
  const assumptions = rules.slice(0, length - 1)
  let name;
  // declare constants to be used in proof
  constants.forEach(element => {
    name = element.value
    file_contents += '(declare-const ' + name + ' Bool)\n'
  });

  // translate assumptions
  assumptions.forEach(element => {
    file_contents += '(assert ' + translate_rule(element) + ')\n'
  })
  
  // translate AND NEGATE goal
  const negated_goal = '(assert (not '+ translate_rule(goal) + '))\n'
  file_contents += negated_goal
  file_contents += '(check-sat)'
  fs.writeFileSync(proof_file_name, file_contents)
}
module.exports = translate_to_SMT;


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
  let lhsExpr = translate_rule(rule.lhs)
  let rhsExpr = translate_rule(rule.rhs)
  return '(and ' + lhsExpr + ' ' + rhsExpr + ')'

}

function translate_or_rule(rule) {
  let lhsExpr = translate_rule(rule.lhs)
  let rhsExpr = translate_rule(rule.rhs)
  return '(or ' + lhsExpr + ' ' + rhsExpr + ')'
}

function translate_implies_rule(rule) {
  let lhsExpr = translate_rule(rule.lhs)
  let rhsExpr = translate_rule(rule.rhs)
  return '(=> ' + lhsExpr + ' ' + rhsExpr + ')'
}

function translate_iff_rule(rule) {
  const expr1 = translate_rule(rule.lhs)
  const expr2 = translate_rule(rule.rhs)
  return '(iff '+ expr1 + ' ' + expr2 + ')'
}

function translate_not_rule(rule) {
  return '(not '+ translate_rule(rule.value) + ')'
}

function translate_literal(rule) {
  return rule.value
}

// translate_to_SMT(test_rules, test_constants)
// translate_to_SMT(test_rules2, test_constants2)
// translate_to_SMT(test_rules3, test_constants3)
