const fs = require('fs')
const {random_file_name} = require('../utils')

const declare_atoms = (atoms, file_contents) => {
  console.log("Atoms")
  console.log(atoms)
  atoms.forEach(element => {
    if (element.value) {
      let varType = "Type"
      if (element.varType) {
        varType = element.varType
      }
      file_contents += '(declare-const ' + element.value + ' ' + varType + ')\n'
    }
  })
  return file_contents
}

const declare_constants = (constants, file_contents) => {
  console.log("CONSTANTS")
  console.log(constants)
  constants.forEach(element => {
    if (element) {
      let varType = "Any"
      if (element.varType) {
        varType = element.varType
      }
      file_contents += '(declare-const ' + element + ' '+varType+')\n'
    }
  })
  return file_contents
}

const declare_relations = (relations, file_contents) => {
  file_contents += '(declare-sort Any)\n'
  console.log("RELATIONS#######")
  console.log(relations)
  relations.forEach(rel => {
    file_contents += '(declare-fun ' + rel.name + ' ('
    console.log(rel)
    console.log("REL#######")
    rel.params.forEach(p => {
      file_contents += '(' + p.varType + ')'
    })
    // file_contents += [...Array(rel.params)].map(p => '(' + p.varType + ')').join(" ") // need to change to the type of the params
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
      if (element.type == 'funcDef') {
        file_contents += translate_func_declaration(element)
      } else {
        file_contents += '(assert ' + translate_rule(element) + ')\n'
      }
    }
  })
  return file_contents
}

const translate_func_declaration = (func) => {
  let file_contents = '(declare-fun ' + func.name + ' ('
  func.params.forEach(type => {
    file_contents += type.value + ' '
  })
  file_contents += ') ' + func.returnType.value + ')\n'
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
    default: return translate_literal(rule)
  }
}

const translate_unary_rule = (rule) => {
  switch (rule.symbol) {
    case 'not': return translate_not_rule(rule)
    default: return translate_literal(rule)
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
    case 'case': return translate_or_rule(rule)
    case 'paren': return translate_rule(rule.value)
    case 'sq_paren': return translate_rule(rule)
    case 'universal_quantifier': case 'existential_quantifier': return translate_quantifier(rule)
    case 'relation': return translate_relation(rule)
    case 'assume': return translate_assume(rule)
    case 'exit': return
    case 'variable': return translate_variable(rule)
    default: return translate_literal(rule)
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
  translation += rule.params.map(v => translate_rule(v)).join(" ")
  translation += ')'
  return translation
}

const translate_and_rule = (rule) => '(and ' + translate_rule(rule.lhs) + ' ' + translate_rule(rule.rhs) + ')'
const translate_or_rule = (rule) => '(or ' +  translate_rule(rule.lhs) + ' ' + translate_rule(rule.rhs) + ')'
const translate_implies_rule = (rule) => '(=> ' + translate_rule(rule.lhs) + ' ' + translate_rule(rule.rhs) + ')'
const translate_iff_rule = (rule) => '(iff '+ translate_rule(rule.lhs) + ' ' + translate_rule(rule.rhs) + ')'
const translate_not_rule = (rule) => '(not '+ translate_rule(rule.value) + ')'
const translate_assume = (rule) => translate_rule(rule.value)
const translate_literal = (rule) => rule.value

const translate = (rules, constants, relations, atoms, types) => {
  let file_contents = ""
  const length = rules.length
  const goal = rules.slice(length - 1)[0]
  const assumptions = rules.slice(0, length - 1)
  file_contents = declare_types(types, file_contents)
  file_contents = declare_relations(relations, file_contents)
  file_contents = declare_constants(constants, file_contents)
  file_contents = declare_atoms(atoms, file_contents)
  file_contents = translate_assumptions(assumptions, file_contents)
  file_contents = translate_goal(goal, file_contents)
  console.log(file_contents)
  return file_contents
}

const translate_and_save = (rules, constants, relations, atoms, types) => {
  const file_contents = translate(rules, constants, relations, atoms, types)
  const proof_file_name = random_file_name()
  fs.writeFileSync(proof_file_name, file_contents)
  return proof_file_name
}

module.exports = { translate_and_save, translate }
