const crypto = require('crypto')

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

const validate_dependencies = (step, dependency, givens, allSteps) => {
  if (dependency <= givens.length) {
    return (givens[dependency-1] && givens[dependency-1].ast) || null
  }
  else {
    // Using a step dependency, check scope is valid
    if (allSteps[dependency-givens.length-1].scope.filter(s => step.scope.indexOf(s) === -1).length === 0) {
      return (allSteps[dependency-givens.length-1] && allSteps[dependency-givens.length-1].ast) || null
    }
    return false
  }
}

module.exports = { is_step, scan_state, random_file_name, validate_dependencies }