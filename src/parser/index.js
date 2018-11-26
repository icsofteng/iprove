const { InputStream, CommonTokenStream } = require('antlr4')
const { iProveLexer } = require('./iProveLexer')
const { iProveParser } = require('./iProveParser')
const { iProveVisitor } = require('./iProveVisitor')

const parse = (input, identifiers_existing = [], relations_existing = [], functions_existing = []) => {
  const chars = new InputStream(input)
  const lexer = new iProveLexer(chars)
  const tokens  = new CommonTokenStream(lexer)
  const parser = new iProveParser(tokens)
  const visitor = new iProveVisitor(identifiers_existing, relations_existing, functions_existing)
  parser.buildParseTrees = true
  const tree = parser.statement()
  const ast = visitor.visitStatement(tree)
  const identifiers = visitor.getIdentifiers()
  const relations = visitor.getRelations()
  const types = visitor.getTypes()
  const functions = visitor.getFunctions()
  const errors = visitor.getErrors()
  return { ast, identifiers, relations, types, functions, errors }
}

exports.parse = parse
