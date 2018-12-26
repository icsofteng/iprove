const fs = require('fs')
const {random_file_name} = require('../utils')

const declare_identifiers = (identifiers, file_contents) => {
  identifiers.forEach(element => {
    if (element) {
      file_contents += '(declare-const ' + element.value + ' '+element.varType+')\n'
    }
  })
  return file_contents
}

const declare_functions = (functions, file_contents) => {
  functions.forEach(func => {
    file_contents += '(declare-fun ' + func.name + ' ('
    func.params.forEach(p => {
      file_contents += '(' + p + ')'
    })
    file_contents += ') '+func.rType+')\n'
  })
  return file_contents
}

const declare_relations = (relations, file_contents) => {
  relations.forEach(rel => {
    file_contents += '(declare-fun ' + rel.name + ' ('
    rel.params.forEach(p => {
      file_contents += '(' + p + ')'
    })
    file_contents += ') Bool)\n'
  })
  return file_contents
}

const declare_types = (types, file_contents) => {
  types.forEach(type => {
    file_contents += '(declare-sort '+ type + ')\n'
  })
  return file_contents
}

const translate_assumptions = (assumptions, file_contents) => {
  assumptions.forEach(element => {
    if (element) {
      if (element.type !== 'identifier' || (element.type === 'identifier' && element.varType === "Bool")) {
        const translation = translate_rule(element)
        if (translation) {
          file_contents += '(assert ' + translation + ')\n'
        }
      }
    }
  })
  return file_contents
}

const translate_goal = (goal, file_contents) => {
  if (goal) {
    var negated_goal = '(assert (not '+ translate_rule(goal) + '))\n'
    file_contents += negated_goal
    file_contents += '(check-sat)'
    return file_contents
  }
}

const translate_binary_rule = (rule) => {
  switch (rule.symbol) {
    case 'and': return translate_and_rule(rule)
    case 'or': return translate_or_rule(rule)
    case 'iff': return translate_iff_rule(rule)
    case 'implies': return translate_implies_rule(rule)
    default: return translate_identifier(rule)
  }
}

const translate_unary_rule = (rule) => {
  switch (rule.symbol) {
    case 'not': return translate_not_rule(rule)
    default: return translate_identifier(rule)
  }
}

const translate_variable = ({ value }) => value

const translate_binary_numerical = (rule) => {
  switch (rule.symbol) {
    case 'less_than': return translate_less_than(rule)
    case 'less_than_eq': return translate_less_than_eq(rule)
    case 'greater_than': return translate_greater_than(rule)
    case 'greater_than_eq': return translate_greater_than_eq(rule)
    case 'equal': return translate_equal(rule)
    case 'plus': return translate_plus(rule)
    case 'minus': return translate_minus(rule)
    case 'power': return translate_power(rule)
    case 'multiply': return translate_multiply(rule)
    case 'divide': return translate_divide(rule)
    default: return ''
  }
}

const translate_less_than = (rule) => '(< ' + translate_rule(rule.lhs) + ' ' + translate_rule(rule.rhs) + ')'
const translate_less_than_eq = (rule) => '(<= ' + translate_rule(rule.lhs) + ' ' + translate_rule(rule.rhs) + ')'
const translate_greater_than = (rule) => '(> ' + translate_rule(rule.lhs) + ' ' + translate_rule(rule.rhs) + ')'
const translate_greater_than_eq = (rule) => '(>= ' + translate_rule(rule.lhs) + ' ' + translate_rule(rule.rhs) + ')'
const translate_equal = (rule) => '(= ' + translate_rule(rule.lhs) + ' ' + translate_rule(rule.rhs) + ')'
const translate_plus = (rule) => '(+ ' + translate_rule(rule.lhs) + ' ' + translate_rule(rule.rhs) + ')'
const translate_minus = (rule) => '(- ' + translate_rule(rule.lhs) + ' ' + translate_rule(rule.rhs) + ')'
const translate_power = (rule) => '(^ ' + translate_rule(rule.lhs) + ' ' + translate_rule(rule.rhs) + ')'
const translate_multiply = (rule) => '(* ' + translate_rule(rule.lhs) + ' ' + translate_rule(rule.rhs) + ')'
const translate_divide = (rule) => '(/ ' + translate_rule(rule.lhs) + ' ' + translate_rule(rule.rhs) + ')'

const translate_rule = (rule) => {
  switch (rule.type) {
    case 'binary': return translate_binary_rule(rule)
    case 'binary_numerical': return translate_binary_numerical(rule)
    case 'unary': return translate_unary_rule(rule)
    case 'true':
    case 'false': return rule.type
    case 'case': return
    case 'paren': return translate_rule(rule.value)
    case 'sq_paren': return translate_rule(rule.value)
    case 'universal_quantifier': case 'existential_quantifier': return translate_quantifier(rule)
    case 'relation': return translate_relation(rule)
    case 'assume': return translate_assume(rule)
    case 'exit': return
    case 'arbitrary': return translate_arbitrary(rule)
    case 'variable': return translate_variable(rule)
    default: return translate_identifier(rule)
  }
}

const translate_quantifier = ({ symbol, variables, value }) => {
  let vars = ''
  variables.forEach(v => {
    if (v.varType) vars = vars + '(' + v.value + ' ' + v.varType + ')'
    else vars = vars + '(' + v.value + ')'
  })
  return '(' + symbol + ' (' + vars + ')' + translate_rule(value) + ')'
}

const translate_relation = (rule) => {
  let translation = '(' + rule.name + ' '
  translation += rule.params.map(v => v.value).join(" ")
  translation += ')'
  return translation
}

const translate_arbitrary = (rule) =>
  '(forall ((somevar ' + rule.value.varType + ')) (= somevar ' + rule.value.value + '))'

const translate_and_rule = (rule) => '(and ' + translate_rule(rule.lhs) + ' ' + translate_rule(rule.rhs) + ')'
const translate_or_rule = (rule) => '(or ' +  translate_rule(rule.lhs) + ' ' + translate_rule(rule.rhs) + ')'
const translate_implies_rule = (rule) => '(=> ' + translate_rule(rule.lhs) + ' ' + translate_rule(rule.rhs) + ')'
const translate_iff_rule = (rule) => '(iff '+ translate_rule(rule.lhs) + ' ' + translate_rule(rule.rhs) + ')'
const translate_not_rule = (rule) => '(not '+ translate_rule(rule.value) + ')'
const translate_assume = (rule) => translate_rule(rule.value)
const translate_identifier = (rule) => rule.value

const translate = (rules, identifiers, relations, types, functions) => {
  let file_contents = ""
  const length = rules.length
  const goal = rules.slice(length - 1)[0]
  const assumptions = rules.slice(0, length - 1)
  file_contents = declare_types(types, file_contents)
  file_contents = declare_functions(functions, file_contents)
  file_contents = declare_relations(relations, file_contents)
  file_contents = declare_identifiers(identifiers, file_contents)
  file_contents = translate_assumptions(assumptions, file_contents)
  file_contents = translate_goal(goal, file_contents)
  return file_contents
}

const translate_and_save = (rules, identifiers, relations, types, functions) => {
  const file_contents = translate(rules, identifiers, relations, types, functions)
  const proof_file_name = random_file_name()
  fs.writeFileSync(proof_file_name, file_contents)
  return proof_file_name
}

module.exports = { translate_and_save, translate }
