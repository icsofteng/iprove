export const is_step = (step) =>
  Boolean(step) && step.ast && Object.keys(step.ast).length > 0

export const scan_state = (state, path, key) => {
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