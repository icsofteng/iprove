const { InputStream, CommonTokenStream } = require('antlr4')
const { PropositionalLexer } = require('./PropositionalLexer')
const { PropositionalParser } = require('./PropositionalParser')
const { PropositionalVisitor } = require('./PropositionalVisitor')
const util = require('util')

const parse = (input) => {
  const chars = new InputStream(input)
  const lexer = new PropositionalLexer(chars)
  const tokens  = new CommonTokenStream(lexer)
  const parser = new PropositionalParser(tokens)
  const visitor = new PropositionalVisitor()
  parser.buildParseTrees = true
  const tree = parser.statement()
  const ast = visitor.visitStatement(tree)
  const constants = visitor.getConstants()
  return { ast, constants }
}

exports.parse = parse