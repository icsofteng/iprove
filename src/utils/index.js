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
    return { depth, index: path[i] }
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

const validate_step_dependencies = (step, dependencies, givens, allSteps) => {
  // Normal case: loop through each dependecy individually
  let valid_deps = dependencies.map(d => {
    const dependencyStep = calculate_dependency_offset(allSteps, d, givens)
    if (d <= givens.length) {
      return (dependencyStep && dependencyStep.ast) || null
    }
    else {
      if (dependency_in_scope(step, dependencyStep)) {
        return (dependencyStep && dependencyStep.ast) || null
      }
      return null
    }
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

  return valid_deps
}

module.exports = { is_step, scan_state, random_file_name, validate_step_dependencies }