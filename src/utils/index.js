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

const is_valid_dependency = (step, dependencyStep, allSteps, givens) => {
  // Make sure no dependencies have a scope that the step's scope contains
  if (dependencyStep.scope.filter(s => step.scope.indexOf(s) === -1).length === 0) {
    return true
  }
  // Allow assumptions
  if (step.ast.symbol === 'implies' &&
     ((dependencyStep.ast.type === 'assume' && equal_ast(step.ast.lhs, dependencyStep.ast.value)) ||
      equal_ast(step.ast.rhs, dependencyStep.ast)
     ) &&
     (_.isEqual(dependencyStep.scope.slice(0, -1), step.scope))) {
    return true
  }
  // Allow case analysis
  if ((dependencyStep.ast.type !== 'case' && step.dependencies.filter(d => calculate_dependency_step(allSteps, d, givens).ast.type === 'case').length > 0) ||
      (dependencyStep.ast.type === 'case' && _.isEqual(dependencyStep.scope, step.scope) &&
      step.dependencies
        .filter(d => calculate_dependency_step(allSteps, d, givens).ast.type === 'assume')
        .filter(d => {
          let dStep = calculate_dependency_step(allSteps, d, givens)
          let scopeEqual = _.isEqual(dStep.scope.slice(0, -1), step.scope)
          let matchesLhs = _.isEqual(dStep.ast.value, dependencyStep.ast.lhs)
          let matchesRhs = _.isEqual(dStep.ast.value, dependencyStep.ast.rhs)
          return scopeEqual && (matchesLhs || matchesRhs)
        }).length === 2 &&
      step.dependencies
        .filter((d, i) => {
          let dStep = calculate_dependency_step(allSteps, d, givens)
          if (_.isEqual(dStep.scope.slice(0, -1), step.scope)) {
            for (let j in step.dependencies) {
              if (j !== i && _.isEqual(calculate_dependency_step(allSteps, step.dependencies[j], givens).ast, dStep.ast)) {
                return _.isEqual(calculate_dependency_step(allSteps, step.dependencies[j], givens).scope.slice(0, -1), dStep.scope.slice(0, -1))
              }
            }
          }
          return false
        }).length >= 1
      )) {
    return true
  }
  return false
}

const calculate_dependency_step = (steps, dependency, givens) => {
  if (dependency <= givens.length) {
    return givens[dependency-1]
  }
  else {
    return steps[dependency-givens.length-1]
  }
}

const validate_dependencies = (step, dependency, givens, allSteps) => {
  const dependencyStep = calculate_dependency_step(allSteps, dependency, givens)
  if (dependency <= givens.length) {
    return (dependencyStep && dependencyStep.ast) || null
  }
  else {
    // Using a step dependency, check scope is valid
    if (is_valid_dependency(step, dependencyStep, allSteps, givens)) {
      return (dependencyStep && dependencyStep.ast) || null
    }
    return null
  }
}

module.exports = { is_step, scan_state, random_file_name, validate_dependencies }