const fs = require('fs')
const crypto = require('crypto')

const random_file_name = () => {
  const current_date = (new Date()).valueOf().toString()
  const random = Math.random().toString()
  return crypto.createHash('sha1').update(current_date + random).digest('hex').toString()
}

const declare_constants = (constants, file_contents) => {
  constants.forEach(element => {
    const name = element.value
    file_contents += '(declare-const ' + name + ' Bool)\n'
  });
  return file_contents
}

const translate_assumptions = (assumptions, file_contents) => {
  assumptions.forEach(element => {
    file_contents += '(assert ' + translate_rule(element) + ')\n'
  })
  return file_contents
}

const translate_goal = (goal, file_contents) => {
  var negated_goal = '(assert (not '+ translate_rule(goal) + '))\n'
  file_contents += negated_goal
  file_contents += '(check-sat)'
  return file_contents
}

const translate_rule = (rule) => {
  switch (rule.type) {
    case 'and': return translate_and_rule(rule)
    case 'or': return translate_or_rule(rule)
    case 'not': return translate_not_rule(rule)
    case 'iff': return translate_iff_rule(rule)
    case 'implies': return translate_implies_rule(rule)
    default: return translate_literal(rule)
  }
}   

const translate_and_rule = (rule) => '(and ' + translate_rule(rule.lhs) + ' ' + translate_rule(rule.rhs) + ')'
const translate_or_rule = (rule) => '(or ' +  translate_rule(rule.lhs) + ' ' + translate_rule(rule.rhs) + ')'
const translate_implies_rule = (rule) => '(=> ' + translate_rule(rule.lhs) + ' ' + translate_rule(rule.rhs) + ')'
const translate_iff_rule = (rule) => '(iff '+ translate_rule(rule.lhs) + ' ' + translate_rule(rule.rhs) + ')'
const translate_not_rule = (rule) => '( not '+ translate_rule(rule.value) + ')'
const translate_literal = (rule) => rule.value

const translate = (rules, constants) => {
  const proof_file_name = random_file_name()
  let file_contents = ""

  // split goal and assumptions
  const length = rules.length
  const goal = rules.slice(length - 1)[0]
  const assumptions = rules.slice(0, length - 1)

  file_contents = declare_constants(constants, file_contents)
  file_contents = translate_assumptions(assumptions, file_contents)
  file_contents = translate_goal(goal, file_contents)
  fs.writeFile(proof_file_name, file_contents, (err)=>{})
}

export default translate