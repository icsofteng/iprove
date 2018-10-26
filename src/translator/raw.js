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

const translate_quantifier = (rule) => {
  return rule.symbol + ' ' + rule.variable + ' (' + translate_rule(rule.value) + ')'
}

const translate_relation = (rule) => {
  let translation = rule.name + '('
  rule.params.forEach(v => {
    translation += ', '
    translation += v
  })
  translation += ')'
  return translation
}

const translate_rule = (rule) => {
  if (rule) {
    switch (rule.type) {
      case 'binary': return translate_binary_rule(rule)
      case 'unary' : return translate_unary_rule(rule)
      case 'true':
      case 'false': return rule.type
      case 'paren': return translate_paren(rule)
      case 'quantifier': return translate_quantifier(rule)
      case 'relation': return translate_relation(rule)
      default: return translate_literal(rule)
    }
  }
} 

const translate_and_rule = (rule) => translate_rule(rule.lhs) + ' and ' + translate_rule(rule.rhs)
const translate_or_rule = (rule) => translate_rule(rule.lhs) + ' or ' + translate_rule(rule.rhs)
const translate_implies_rule = (rule) => translate_rule(rule.lhs) + ' implies ' + translate_rule(rule.rhs)
const translate_iff_rule = (rule) => translate_rule(rule.lhs) + ' iff ' + translate_rule(rule.rhs)
const translate_not_rule = (rule) => 'not ' + translate_rule(rule.value)
const translate_literal = (rule) => rule.value
const translate_paren = (rule) => '(' + translate_rule(rule.value) + ')'

const translate = (rules) =>
  rules.map(rule => translate_rule(rule))

module.exports = { translate, translate_rule }