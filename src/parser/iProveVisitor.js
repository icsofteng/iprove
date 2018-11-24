const _ = require('underscore')
const { tree } = require('antlr4')
const { ParseTreeVisitor } = tree

_.mixin({
  capitalize: function(string) {
    return string.charAt(0).toUpperCase() + string.substring(1).toLowerCase()
  }
})

class iProveVisitor extends ParseTreeVisitor {
  constructor() {
    super()
    this.identifiers = []
    this.relations = []
    this.types = []
    this.base_types = ['Int', 'Bool', 'Real', 'BitVec 4', 'Array', 'Set', 'Pair']
    this.variables_quantifiers = []
  }

  // Recursive definitions
  visitStatement(ctx) {
    return this.visitChildren(ctx)
  }
  visitIdentifierExp(ctx) {
    return this.visit(ctx.ident())
  }

  // Relations and functions
  visitRelationExp(ctx) {
    const name = ctx.IDENTIFIER().toString()
    const params = ctx.ident().map(param => this.visit(param))
    if (this.relations.indexOf(name) === -1) {
      this.relations.push({name, numParam: params.length, params})
    }
    return { type: 'relation', name, params }
  }
  visitRelationDefExp(ctx) {
    const identifiers = ctx.IDENTIFIER()
    const name = identifiers.shift().toString()
    let rType = _.capitalize(identifiers.pop().toString())
    if ((this.types.indexOf(rType) === -1) && (this.base_types.indexOf(rType) === -1)) {
      this.types.push(rType)
    }
    const params = identifiers.map(para => {
      para = {type: 'type', value: para.toString()}
      para.value = _.capitalize(para.value)
      if ((this.types.indexOf(para.value) === -1) && (this.base_types.indexOf(para.value) === -1)) {
        this.types.push(para.value)
      }
     return para
    }) || []

    return { type: 'funcDef', name, params, returnType: {type: 'type', value: rType} }
  }
  visitIdentRule(ctx) {
    const lit = ctx.IDENTIFIER()[0].toString()
    let varType = ctx.IDENTIFIER()[1]
    if (varType) {
      varType = _.capitalize(varType.toString())
      if ((this.types.indexOf(varType) === -1) && (this.base_types.indexOf(varType) === -1)) {
        this.types.push(varType)
      }
    }
    else {
      const findPrevDefinedVariable = this.variables_quantifiers.find(({ value }) => value === lit)
      varType = findPrevDefinedVariable ? findPrevDefinedVariable.varType : "Bool"
    }
    if (!this.variables_quantifiers.find(({ value }) => value === lit)) {
      this.identifiers.push({ value: lit, varType })
      this.identifiers = _.uniq(this.identifiers, false, _.iteratee('value'))
    }
    return { type: 'identifier', value: lit , varType}
  }

  // Quantifiers
  visitForallExp(ctx) {
    const variables = ctx.ident().map(varDef => {
      const thisVar = this.visit(varDef)
      this.variables_quantifiers.push(thisVar)
      this.identifiers = this.identifiers.filter(ident => thisVar.value !== ident.value)
      return thisVar
    })
    let value = this.visit(ctx.expression())
    return { type: 'universal_quantifier', symbol: 'forall', variables, value }
  }
  visitExistsExp(ctx) {
    const value = this.visit(ctx.expression())
    const variables = ctx.ident().map(varDef => {
      const thisVar = this.visit(varDef)
      this.variables_quantifiers.push(thisVar)
      this.identifiers = this.identifiers.filter(ident => thisVar.value !== ident.value)
      return thisVar
    })
    return { type: 'existential_quantifier', symbol: 'exists', variables, value }
  }

  // Numerical visitors
  visitLessThanExp(ctx) {
    const lhs = this.visit(ctx.expression()[0])
    const rhs = this.visit(ctx.expression()[1])
    return { type: 'binary_numerical', symbol: 'less_than', lhs, rhs }
  }
  visitLessThanEqExp(ctx) {
    const lhs = this.visit(ctx.expression()[0])
    const rhs = this.visit(ctx.expression()[1])
    return { type: 'binary_numerical', symbol: 'less_than_eq', lhs, rhs }
  }
  visitGreaterThanExp(ctx) {
    const lhs = this.visit(ctx.expression()[0])
    const rhs = this.visit(ctx.expression()[1])
    return { type: 'binary_numerical', symbol: 'greater_than', lhs, rhs }
  }
  visitGreaterThanEqExp(ctx) {
    const lhs = this.visit(ctx.expression()[0])
    const rhs = this.visit(ctx.expression()[1])
    return { type: 'binary_numerical', symbol: 'greater_than_eq', lhs, rhs }
  }
  visitEqualExp(ctx) {
    const lhs = this.visit(ctx.expression()[0])
    const rhs = this.visit(ctx.expression()[1])
    return { type: 'binary_numerical', symbol: 'equal', lhs, rhs }
  }
  visitPlusExp(ctx) {
    const lhs = this.visit(ctx.expression()[0])
    const rhs = this.visit(ctx.expression()[1])
    return { type: 'binary_numerical', symbol: 'plus', lhs, rhs }
  }
  visitMinusExp(ctx) {
    const lhs = this.visit(ctx.expression()[0])
    const rhs = this.visit(ctx.expression()[1])
    return { type: 'binary_numerical', symbol: 'minus', lhs, rhs }
  }
  visitPowerExp(ctx) {
    const lhs = this.visit(ctx.expression()[0])
    const rhs = this.visit(ctx.expression()[1])
    return { type: 'binary_numerical', symbol: 'power', lhs, rhs }
  }
  visitMultiplyExp(ctx) {
    const lhs = this.visit(ctx.expression()[0])
    const rhs = this.visit(ctx.expression()[1])
    return { type: 'binary_numerical', symbol: 'multiply', lhs, rhs }
  }
  visitDivideExp(ctx) {
    const lhs = this.visit(ctx.expression()[0])
    const rhs = this.visit(ctx.expression()[1])
    return { type: 'binary_numerical', symbol: 'divide', lhs, rhs }
  }
  visitIntegerExp(ctx) {
    const value = parseInt(ctx.INTEGER().toString())
    return { type: 'integer', value }
  }
  visitRealExp(ctx) {
    const value = parseFloat(ctx.REAL().toString())
    return { type: 'real', value }
  }

  // Simple types
  visitCaseExp(ctx) {
    return { type: 'case' }
  }
  visitAssumeExp(ctx) {
    const value = this.visit(ctx.expression())
    return { type: 'assume', value }
  }
  visitArbitraryExp(ctx) {
    const constant = this.visit(ctx.expression())
    this.constants.push({ value: constant.value, varType: constant.varType })
    return { type: 'arbitrary', value: constant }
  }
  visitExitExp(ctx) {
    return { type: 'exit' }
  }
  visitParenthesesExp(ctx) {
    const value = this.visit(ctx.expression())
    return { type: 'paren', value }
  }
  visitSqParenthesesExp(ctx) {
    const value = this.visit(ctx.expression())
    return { type: 'sq_paren', value }
  }
  visitNotExp(ctx) {
    const value = this.visit(ctx.expression())
    return { type: 'unary', symbol: 'not', value }
  }
  visitTrueExp(ctx) {
    return { type: 'true' }
  }
  visitFalseExp(ctx) {
    return { type: 'false' }
  }

  // Binary operators
  visitAndExp(ctx) {
    const lhs = this.visit(ctx.expression()[0])
    const rhs = this.visit(ctx.expression()[1])
    return { type: 'binary', symbol: 'and', lhs, rhs }
  }
  visitOrExp(ctx) {
    const lhs = this.visit(ctx.expression()[0])
    const rhs = this.visit(ctx.expression()[1])
    return { type: 'binary', symbol: 'or', lhs, rhs }
  }
  visitImpliesExp(ctx) {
    const lhs = this.visit(ctx.expression()[0])
    const rhs = this.visit(ctx.expression()[1])
    return { type: 'binary', symbol: 'implies', lhs, rhs }
  }
  visitIffExp(ctx) {
    const lhs = this.visit(ctx.expression()[0])
    const rhs = this.visit(ctx.expression()[1])
    return { type: 'binary', symbol: 'iff', lhs, rhs }
  }

  // Getter methods
  getAtoms() {
    return this.atoms
  }
  getIdentifiers() {
    return this.identifiers
  }
  getRelations() {
    return this.relations
  }
  getTypes() {
    return this.types
  }

}

exports.iProveVisitor = iProveVisitor
