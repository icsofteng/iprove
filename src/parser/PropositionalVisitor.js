const util = require('util')
const { tree } = require('antlr4')
const { ParseTreeVisitor } = tree

class PropositionalVisitor extends ParseTreeVisitor {
  constructor(response) {
    super()
    this.response = response
  }

	visitExpression(ctx) {
    this.response.write(util.inspect(ctx))
    return this.visitChildren(ctx)
  }
}

module.exports = { PropositionalVisitor }