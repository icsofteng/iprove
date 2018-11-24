const { InputStream, CommonTokenStream } = require('antlr4')
const { iProveLexer } = require('./iProveLexer')
const { iProveParser } = require('./iProveParser')
const { iProveVisitor } = require('./iProveVisitor')

const parse = (input) => {
  const chars = new InputStream(input)
  const lexer = new iProveLexer(chars)
  const tokens  = new CommonTokenStream(lexer)
  const parser = new iProveParser(tokens)
  const visitor = new iProveVisitor()
  parser.buildParseTrees = true
  const tree = parser.statement()
  const ast = visitor.visitStatement(tree)
  const identifiers = visitor.getIdentifiers()
  const relations = visitor.getRelations()
  const types = visitor.getTypes()
  return { ast, identifiers, relations, types }
}

exports.parse = parse
