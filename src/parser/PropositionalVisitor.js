const { tree } = require('antlr4')
const { ParseTreeVisitor } = tree

class PropositionalVisitor extends ParseTreeVisitor {
	visitExpression(ctx) {
    if (ctx.IMPLIES()) {
      const lhs = this.visitExpression(ctx.expression()[0])
      const rhs = this.visitExpression(ctx.expression()[1])
      return { type: 'binary', symbol: 'implies', lhs, rhs }
    }
    else if (ctx.LITERAL()) {
      return { type: 'literal', value: ctx.LITERAL().toString() }
    }
    else {
      return { type: 'unknown '}
    }
  }
}

module.exports = { PropositionalVisitor }