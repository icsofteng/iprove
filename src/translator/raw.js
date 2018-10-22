const translate_rule = (rule) => {
  if (rule) {
    if (rule.type === 'binary') {
      switch (rule.symbol) {
        case 'and': return translate_and_rule(rule)
        case 'or': return translate_or_rule(rule)
        case 'iff': return translate_iff_rule(rule)
        case 'implies': return translate_implies_rule(rule)
        default: return translate_literal(rule)
      }
    }
    else if (rule.type === 'unary') {
      switch (rule.symbol) {
        case 'not': return translate_not_rule(rule)
        default: return translate_literal(rule)
      }
    }
    else if (rule.type === 'true') {
      return 'true'
    }
    else if (rule.type === 'false') {
      return 'false'
    }
    else {
      return translate_literal(rule)
    }
  }
  return ''
}   

const translate_and_rule = (rule) => translate_rule(rule.lhs) + ' and ' + translate_rule(rule.rhs)
const translate_or_rule = (rule) => translate_rule(rule.lhs) + ' or ' + translate_rule(rule.rhs)
const translate_implies_rule = (rule) => translate_rule(rule.lhs) + ' implies ' + translate_rule(rule.rhs)
const translate_iff_rule = (rule) => translate_rule(rule.lhs) + ' iff ' + translate_rule(rule.rhs)
const translate_not_rule = (rule) => 'not ' + translate_rule(rule.value)
const translate_literal = (rule) => rule.value

const translate = (rules) =>
  rules.map(rule => translate_rule(rule))

module.exports = { translate, translate_rule }