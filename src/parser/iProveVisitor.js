const _ = require('underscore')
const { tree } = require('antlr4')
const { ParseTreeVisitor } = tree

_.mixin({
  capitalize: function(string) {
    return string.charAt(0).toUpperCase() + string.substring(1).toLowerCase()
  }
})

class iProveVisitor extends ParseTreeVisitor {
  constructor(identifiers, relations, functions) {
    super()
    this.identifiers = identifiers
    this.relations = relations
    this.types = []
    this.functions = functions
    this.base_types = ['Int', 'Bool', 'Real', 'BitVec 4', 'Array', 'Set', 'Pair']
    this.variables_quantifiers = []
    this.errors = false
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
    const rel_name = ctx.IDENTIFIER().toString()
    const params = ctx.ident().map(param => this.visit(param))
    const existing_func = this.functions.find(({ name }) => name === rel_name)
    const existing_rel = this.relations.find(({ name }) => name === rel_name)
    if (!existing_rel && !existing_func) {
      this.relations.push({name: rel_name, numParam: params.length, params})
    } else {
      if (params.length == existing_rel.params.length) {
        for (let i = 0; i < params.length; i++) {
          if (params[i].varType != existing_rel.params[i].varType) {
            this.errors = true
          }
        }
      }

      // if you havent errored and this use of a relation (with these params) is not in list, add it
      if (!this.errors) {
        const existing_use = this.relations.find(({name, ps}) => name === rel_name && params ==ps)
        if (!existing_use) {
          this.relations.push({name: rel_name, numParam: params.length, params})
        }
        
      }
    }
    return { type: 'relation', name:rel_name, params }
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
    })
    const findPrevDefinedFunction = this.functions.find(({ name: func_name }) => func_name === name)
    if (!findPrevDefinedFunction) {
      this.functions.push({ name, params: params.map(p => p.value), rType })
    }
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
      varType = findPrevDefinedVariable? findPrevDefinedVariable.varType :"Bool"
      if (!this.variables_quantifiers.find(({ value }) => value === lit)) {
        const findPrevDefinedConst = this.identifiers.find(({ value }) => value === lit)
        varType = findPrevDefinedConst? findPrevDefinedConst.varType :"Bool"
      }
    }
    if (!this.variables_quantifiers.find(({ value }) => value === lit)) {
      // push ident to front of list so uniq() can discard older definitions e.g. if type has changed and you are adding new def
      this.identifiers.unshift({ value: lit, varType })
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
    const identifier = this.visit(ctx.ident())
    this.identifiers.push({ value: identifier.value, varType: identifier.varType })
    return { type: 'arbitrary', value: identifier }
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
  getFunctions() {
    return this.functions
  }
  getErrors() {
    return this.errors
  }

}

exports.iProveVisitor = iProveVisitor
