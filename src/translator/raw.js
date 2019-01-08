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

const translate_quantifier = ({ symbol, variables, value }) => {
  let vars = variables.map(v => v.value + (v.varType !== "Bool" ? ':' + v.varType : "")).join(", ")
  return symbol + ' ' + vars + '.' + translate_rule(value)
}

const translate_relation = (rule) => {
  let translation = rule.name + '('
  if (rule.params) {
    translation += rule.params.map(v => v.value).join(", ")
  }
  translation += ')'
  return translation
}

const translate_funcDef = ({ name, params, returnType }) => {
  let translation = 'define ' + name + '('
  if (params) {
    translation += params.map(p => p.value).join(", ")
  }
  translation += '): ' + returnType.value
  return translation
}

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

const translate_less_than = (rule) => `${translate_rule(rule.lhs, false)} < ${translate_rule(rule.rhs, false)}`
const translate_less_than_eq = (rule) => `${translate_rule(rule.lhs, false)} <= ${translate_rule(rule.rhs, false)}`
const translate_greater_than = (rule) => `${translate_rule(rule.lhs, false)} > ${translate_rule(rule.rhs, false)}`
const translate_greater_than_eq = (rule) => `${translate_rule(rule.lhs, false)} >= ${translate_rule(rule.rhs, false)}`
const translate_equal = (rule) => `${translate_rule(rule.lhs, false)} == ${translate_rule(rule.rhs, false)}`
const translate_plus = (rule) => `${translate_rule(rule.lhs, false)} + ${translate_rule(rule.rhs, false)}`
const translate_minus = (rule) => `${translate_rule(rule.lhs, false)} - ${translate_rule(rule.rhs, false)}`
const translate_power = (rule) => `${translate_rule(rule.lhs, false)} ^ ${translate_rule(rule.rhs, false)}`
const translate_multiply = (rule) => `${translate_rule(rule.lhs, false)} * ${translate_rule(rule.rhs, false)}`
const translate_divide = (rule) => `${translate_rule(rule.lhs, false)} / ${translate_rule(rule.rhs, false)}`

const translate_rule = (rule, show_type = true) => {
  if (rule) {
    switch (rule.type) {
      case 'binary': return translate_binary_rule(rule)
      case 'binary_numerical': return translate_binary_numerical(rule)
      case 'unary' : return translate_unary_rule(rule)
      case 'true': return 'true'
      case 'false': return 'false'
      case 'exit': return 'exit'
      case 'case': return 'case'
      case 'paren': return translate_paren(rule)
      case 'sq_paren': return translate_sq_paren(rule)
      case 'universal_quantifier': case 'existential_quantifier': return translate_quantifier(rule)
      case 'relation': return translate_relation(rule)
      case 'assume': return translate_assume(rule)
      case 'variable': return translate_variable(rule)
      case 'arbitrary': return 'arbitrary ' + translate_literal(rule.value)
      case 'funcDef': return translate_funcDef(rule)
      default: return translate_literal(rule, show_type)
    }
  }
}

const translate_and_rule = (rule) => translate_rule(rule.lhs) + ' and ' + translate_rule(rule.rhs)
const translate_or_rule = (rule) => translate_rule(rule.lhs) + ' or ' + translate_rule(rule.rhs)
const translate_implies_rule = (rule) => translate_rule(rule.lhs) + ' implies ' + translate_rule(rule.rhs)
const translate_iff_rule = (rule) => translate_rule(rule.lhs) + ' iff ' + translate_rule(rule.rhs)
const translate_not_rule = (rule) => 'not ' + translate_rule(rule.value)
const translate_literal = (rule, show_type = true) => {
  if (rule.varType && rule.varType !== "Bool") {
    return rule.value + (show_type ? ':' + rule.varType : "")
  }
  if (rule.value === undefined) {
    return ' '
  }
  return rule.value
}
const translate_variable = (rule) => rule.value
const translate_paren = (rule, show_type = true) => '(' + translate_rule(rule.value, show_type) + ')'
const translate_sq_paren = (rule, show_type = true) => '[' + translate_rule(rule.value, show_type) + ']'
const translate_assume = (rule) => 'assume ' + translate_rule(rule.value)

module.exports = { translate_rule }
