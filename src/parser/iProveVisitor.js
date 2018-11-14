const { tree } = require('antlr4')
const { ParseTreeVisitor } = tree

class iProveVisitor extends ParseTreeVisitor {
  constructor() {
    super()
    this.atoms = []
    this.constants = []
    this.relations = []
    this.types = []
    this.base_types = ['Int', 'Bool', 'Real', 'BitVec 4', 'Array', 'Set', 'Pair']
  }
  visitStatement(ctx) {
    return this.visitChildren(ctx)
  }
  visitCaseExp(ctx) {
    return { type: 'case' }
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
    const variables = ctx.variableDef().map(varDef => this.visit(varDef))
    return { type: 'universal_quantifier', symbol: 'forall', variables, value }
  }
  visitExistsExp(ctx) {
    const value = this.visit(ctx.expression())
    const variables = ctx.variableDef().map(varDef => this.visit(varDef))
    return { type: 'existential_quantifier', symbol: 'exists', variables, value }
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
    let rType = identifiers[identifiers.length - 1]
    rType = rType.charAt(0).toUpperCase() + rType.slice(1) // z3 doesnt allow lower case types
    const returnType = {type: 'type', value: rType}
    if ((this.types.indexOf(rType) === -1) && (this.base_types.indexOf(rType) === -1)) {
      this.types.push(rType)
    }
    const params = ctx.parameter().map(iden => {
      let para = this.visit(iden)
      para = {type: 'type', value: para.value}
      para.value = para.value.charAt(0).toUpperCase() + para.value.slice(1) // z3 doesnt allow lower case types
      if ((this.types.indexOf(para.value) === -1) && (this.base_types.indexOf(para.value) === -1)) {
        this.types.push(para.value)
      }
     return para
    }) || []

    return {type: 'funcDef', name, params, returnType}
  }
  visitVariableDef(ctx) {
    let varType = ctx.IDENTIFIER()
    if (varType) {
      varType = varType.toString()
      varType = varType.charAt(0).toUpperCase() + varType.slice(1) // z3 doesnt allow lower case types
      if((this.types.indexOf(varType) === -1) && (this.base_types.indexOf(varType) === -1)) {
        this.types.push(varType)
      }
    }
    return {type:'variable', value : ctx.VARIABLE().toString(), varType}
  };
  visitParamType(ctx) {
    let value = ctx.TYPE().toString()
    value = value.charAt(0).toUpperCase() + value.slice(1)  // z3 doesnt allow lower case types
    if ((this.types.indexOf(value) === -1) && (this.base_types.indexOf(value) === -1)) {
      this.types.push(value)
    }
    return {type: 'type', value}
  }
  visitReturnType(ctx) {
    const value = ctx.TYPE().toString()
    return {type: 'type', value}
  }
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
