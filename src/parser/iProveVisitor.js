const { tree } = require('antlr4')
const { ParseTreeVisitor } = tree

class iProveVisitor extends ParseTreeVisitor {
  constructor() {
    super()
    this.atoms = []
    this.constants = []
    this.relations = []
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
    const lit = ctx.LITERAL().toString()
    if (this.atoms.indexOf(lit) === -1) {
      this.atoms.push(lit)
    }
    return { type: 'literal', value: lit }
  }
  visitForallExp(ctx) {
    const value = this.visit(ctx.expression())
    const variable = ctx.VARIABLE().toString()
    return { type: 'quantifier', symbol: 'forall', variable, value }
  }
  visitExistsExp(ctx) {
    const value = this.visit(ctx.expression())
    const variable = ctx.VARIABLE().toString()
    return { type: 'quantifier', symbol: 'exists', variable, value }
  }
  visitRelationExp(ctx) {
    const name = ctx.NAME().toString()
    const params = ctx.parameter().map(param => this.visit(param))
    if (this.relations.indexOf(name) === -1) {
      this.relations.push({name, numParam: params.length})
    }
    return { type: 'relation', name, params }
  }
  visitParamVar(ctx) {
    const value = ctx.VARIABLE().toString()
    return { type: 'variable', value }
  }
  visitParamConst(ctx) {
    const value =  ctx.CONSTANT().toString()
    if (this.constants.indexOf(value) === -1) {
      this.constants.push(value)
    }
    return { type: 'constant', value }
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
}

exports.iProveVisitor = iProveVisitor