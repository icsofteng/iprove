const util = require('util')

class PropositionalVisitor {
  constructor(response) {
    this.response = response
  }

	visitExpression(ctx) {
    this.response.write(util.inspect(ctx))
  }
}

module.exports = { PropositionalVisitor }