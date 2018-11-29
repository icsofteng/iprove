const crypto = require('crypto')
const _ = require('underscore')

const is_step = (step) =>
  Boolean(step) && step.ast && Object.keys(step.ast).length > 0

const scan_state = (state, path, key) => {
  if (path) {
    let depth = state[key]
    let i = 0
    for (; i < path.length - 1; i++) {
      depth = depth[path[i]]
    }
    return { depth, scanIndex: path[i] }
  }
  return state.steps
}

const random_file_name = () => {
  const current_date = (new Date()).valueOf().toString()
  const random = Math.random().toString()
  return crypto.createHash('sha1').update(current_date + random).digest('hex').toString()
}

const equal_ast = (first, second) => {
  let modifiedFirst = first
  let modifiedSecond = second
  modifiedFirst = (modifiedFirst.type === 'paren') ? modifiedFirst.value : modifiedFirst
  modifiedSecond = (modifiedSecond.type === 'paren') ? modifiedSecond.value : modifiedSecond
  return _.isEqual(modifiedFirst, modifiedSecond)
}

const dependency_in_scope = (step, dependencyStep) =>
  dependencyStep.scope.filter(s => step.scope.indexOf(s) === -1).length === 0

const calculate_dependency_offset = (steps, dependency, givens) =>
  (dependency <= givens.length) ? givens[dependency-1] : steps[dependency-givens.length-1]

const extract_out_ors = (ast) => {
  if (ast.type === 'paren') {
    return [extract_out_ors(ast.value)]
  }
  else if (ast.type === 'binary' && ast.symbol === 'or') {
    return extract_out_ors(ast.lhs).concat(extract_out_ors(ast.rhs))
  }
  return [ast]
}

const validate_step_dependencies = (step, dependencies, givens, allSteps) => {
  // Normal case: loop through each dependecy individually
  dependencies = dependencies.filter(Boolean)
  let valid_deps = dependencies.map(d => {
    const dependencyStep = calculate_dependency_offset(allSteps, d, givens)
    if (dependencyStep) {
      if (d <= givens.length) {
        return (dependencyStep && dependencyStep.ast) || null
      }
      else {
        if (dependency_in_scope(step, dependencyStep)) {
          return (dependencyStep && dependencyStep.ast) || null
        }
      }
    }
    return null
  })

  // Special case: we can take an 'implies' out of an assume scope
  if (step.ast.symbol === 'implies' && dependencies.length === 2) {
    const depsClone = dependencies.slice(0)
    const assumeStepNumber = depsClone.filter(d => calculate_dependency_offset(allSteps, d, givens).ast.type === 'assume')[0]
    const assumeStep = calculate_dependency_offset(allSteps, assumeStepNumber, givens)
    depsClone.splice(depsClone.indexOf(assumeStepNumber), 1)
    const assumptionInScope = _.isEqual(assumeStep.scope.slice(0, -1), step.scope)
    const conclusionStep = calculate_dependency_offset(allSteps, depsClone[0], givens)
    const conclusionInScope = _.isEqual(conclusionStep.scope.slice(0, -1), step.scope)
    if (assumptionInScope && conclusionInScope && equal_ast(assumeStep.ast.value, step.ast.lhs) && equal_ast(conclusionStep.ast, step.ast.rhs)) {
      // This is a valid proof justification
      valid_deps = [assumeStep.ast, conclusionStep.ast]
    }
  }

  // Special case: we can take any expression concluded in all cases
  const findCase = dependencies.filter(d => calculate_dependency_offset(allSteps, d, givens).ast.type === 'case')
  if (findCase.length === 1) {
    const depsClone = dependencies.slice(0)
    depsClone.splice(depsClone.indexOf(findCase[0]), 1)
    const findAssumes = depsClone.filter(d => calculate_dependency_offset(allSteps, d, givens).ast.type === 'assume')
    const validateAssumes = findAssumes.map(assumeStepNumber => {
      let assumeStep = calculate_dependency_offset(allSteps, assumeStepNumber, givens)
      depsClone.splice(depsClone.indexOf(assumeStepNumber), 1)
      // The conclusion step must be in the same scope as the assume
      let findConclusion = depsClone.filter(d => _.isEqual(calculate_dependency_offset(allSteps, d, givens).scope, assumeStep.scope))
      if (findConclusion.length === 1) {
        depsClone.splice(depsClone.indexOf(findConclusion[0]), 1)
        let conclusionStep = calculate_dependency_offset(allSteps, findConclusion[0], givens)
        // The conclusion step must match this step
        return equal_ast(conclusionStep.ast, step.ast)
      }
      return false
    })
    if (validateAssumes.every(Boolean)) {
      // We should have one rule left which is an OR
      let remainingRule = calculate_dependency_offset(allSteps, depsClone[0], givens)
      if (depsClone.length === 1 && remainingRule.ast.type === 'binary' && remainingRule.ast.symbol === 'or') {
        const listOfAssumptions = extract_out_ors(remainingRule.ast)
        const orContainsAllAssumes = findAssumes.map(assumeStepNumber => {
          let assumeStep = calculate_dependency_offset(allSteps, assumeStepNumber, givens)
          let assumeAst = assumeStep.ast.value
          return listOfAssumptions.filter(assump => _.isEqual(assumeAst, assump)).length === 1
        })
        if (orContainsAllAssumes.every(Boolean) && findAssumes.length === listOfAssumptions.length) {
          valid_deps = dependencies.map(d => calculate_dependency_offset(allSteps, d, givens).ast)
        }
      }
    }
  }

  return valid_deps
}

module.exports = { is_step, scan_state, random_file_name, validate_step_dependencies }