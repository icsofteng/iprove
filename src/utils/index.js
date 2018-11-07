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

const is_valid_dependency = (step, dependencyStep) => {
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
  return false
}

const validate_dependencies = (step, dependency, givens, allSteps) => {
  if (dependency <= givens.length) {
    return (givens[dependency-1] && givens[dependency-1].ast) || null
  }
  else {
    // Using a step dependency, check scope is valid
    const dependencyStep = allSteps[dependency-givens.length-1]
    if (is_valid_dependency(step, dependencyStep)) {
      return (dependencyStep && dependencyStep.ast) || null
    }
    return null
  }
}

module.exports = { is_step, scan_state, random_file_name, validate_dependencies }