const { tree } = require('antlr4')
const { ParseTreeVisitor } = tree

class iProveVisitor extends ParseTreeVisitor {
  constructor() {
    super()
    this.atoms = []
    this.constants = []
    this.relations = []
    this.types = []
  }
  visitStatement(ctx) {
    return this.visitChildren(ctx)
  }
  visitAssumeExp(ctx) {
    const value = this.visit(ctx.expression())
    return { type: 'assume', value }
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
  visitTrueExp(ctx) {
    return { type: 'true' }
  }
  visitFalseExp(ctx) {
    return { type: 'false' }
  }
  visitLiteralExp(ctx) {
    const lit = ctx.IDENTIFIER().toString()
    if (this.atoms.indexOf(lit) === -1) {
      this.atoms.push(lit)
    }
    return { type: 'literal', value: lit }
  }
  visitForallExp(ctx) {
    const value = this.visit(ctx.expression())
    const variable = { type: 'variable', value: ctx.VARIABLE().toString() }
    return { type: 'universal_quantifier', symbol: 'forall', variable, value }
  }
  visitExistsExp(ctx) {
    const value = this.visit(ctx.expression())
    const variable = { type: 'variable', value: ctx.VARIABLE().toString() }
    return { type: 'existential_quantifier', symbol: 'exists', variable, value }
  }
  visitRelationExp(ctx) {
    const name = ctx.IDENTIFIER().toString()
    const params = ctx.parameter().map(param => {
      let p = this.visit(param)
      if (p.type != 'variable'){
        p = {type: 'constant', value:p.value}
        if (this.constants.indexOf(p.value) === -1) {
          this.constants.push(p.value)
        }
      }
      return p
    }) || []
    if (this.relations.indexOf(name) === -1) {
      this.relations.push({name, numParam: params.length})
    }
    return { type: 'relation', name, params }
  }
  visitRelationDefExp(ctx) {
    const identifiers = ctx.IDENTIFIER().toString().split(',')
    const name = identifiers[0]
    const returnType = {type: 'type', value: identifiers[identifiers.length - 1]}
    const params = ctx.parameter().map(p => {
      if (this.types.indexOf(p.value) === -1) {
        this.types.push(p.value)
      }
     return {type: 'type', value: this.visit(p).value}
    }) || []
  
    console.log(params)
    if (this.relations.indexOf(name) === -1) {
      this.relations.push({name, numParam: params.lentypesgth})
    }
    return {type: 'funcDef', name, params, returnType}
  }

  visitParamType(ctx) {
    const value = ctx.TYPE().toString()
    return {type: 'type', value}
  }

  visitReturnType(ctx) {
    const value = ctx.TYPE().toString()
    return {type: 'type', value}
  }
  visitParamVar(ctx) {
    const value = ctx.VARIABLE().toString()
    return { type: 'variable', value }
  }
  visitParamIdent(ctx) {
    const value =  ctx.IDENTIFIER().toString()
    return { type: 'identifier', value }
  }

  getAtoms() {
    return this.atoms
  }
  getConstants() {
    return this.constants
  }
  getRelations() {
    return this.relations
  }
  getTypes() {
    return this.types
  }
}

exports.iProveVisitor = iProveVisitor
