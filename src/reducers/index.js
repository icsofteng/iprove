import {
  NEW_RULE,
  REMOVE_RULE,
  CHANGE_SYMBOL,
  UPDATE_RULE,
  ADD_CONSTANT,
  ADD_STEP_DEPENDENCY,
  REMOVE_STEP_DEPENDENCY,
  UPDATE_STEP_DEPENDENCY,
} from '../constants'

const initialState = {
  steps: [],
  constants: []
}

const dfs = (state, path) => {
  if (path) {
    let depth = state.steps
    let i = 0
    for (; i < path.length - 1; i++) {
      depth = depth[path[i]]
    }
    return { depth, index: path[i] }
  }
  return state.steps
}

const reducer = (state = initialState, action) => {
  const newState = Object.assign({}, state)
  newState.steps = state.steps.slice(0)
  const { depth, index } = dfs(newState, action.path)

  switch (action.type) {
    case NEW_RULE:
      depth[index] = { type: action.payload }
      return newState

    case UPDATE_RULE:
      depth[index] = action.payload
      return newState

    case REMOVE_RULE:
      delete depth[index]
      return { ...newState, steps: newState.steps.filter(Boolean) }

    case CHANGE_SYMBOL:
      depth[index].symbol = action.payload
      return newState

    case ADD_CONSTANT:
      if (newState.constants.indexOf(action.payload) > -1) {
        return newState
      }
      return { ...newState, constants: [...newState.constants, action.payload] }

    case ADD_STEP_DEPENDENCY:
      depth[index].dependencies = depth[index].dependencies ? [...depth[index].dependencies, null] : [null]
      return newState

    case REMOVE_STEP_DEPENDENCY:
      delete depth[index].dependencies[action.index]
      depth[index].dependencies = depth[index].dependencies.filter(d => d || d === null)
      return newState

    case UPDATE_STEP_DEPENDENCY:
      depth[index].dependencies[action.index] = action.value
      return newState

    default:
      return newState
  }
}

export default reducer
