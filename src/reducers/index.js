import {
  NEW_RULE,
  NEW_STEP,
  REMOVE_RULE,
  CHANGE_SYMBOL,
  UPDATE_RULE,
  ADD_CONSTANTS,
  ADD_STEP_DEPENDENCY,
  ADD_STEP_DEPENDENCY_INDEX,
  REMOVE_STEP_DEPENDENCY,
  UPDATE_STEP_DEPENDENCY,
  SET_STEP_DEPENDENCY
} from '../constants'

const initialState = {
  steps: [{ dependencies: [], ast: {} }],
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
  const newState = JSON.parse(JSON.stringify(state))
  const { depth, index } = dfs(newState, action.path)

  switch (action.type) {
    case NEW_STEP:
      depth[index] = { dependencies: [], ast: { type: action.payload } }
      return newState

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

    case ADD_CONSTANTS:
      const newConstants = newState.constants.concat(action.payload)
      newState.constants = newConstants.filter((item, pos) => newConstants.indexOf(item) === pos)
      return newState

    case SET_STEP_DEPENDENCY:
      if (depth[index]) {
        depth[index] = action.payload.map(x => parseInt(x)).filter(x => !isNaN(x))
      }
      return newState

    case ADD_STEP_DEPENDENCY:
      depth[index] = depth[index] ? [...depth[index], null] : [null]
      return newState

    case ADD_STEP_DEPENDENCY_INDEX:
      depth[index].splice(action.index + 1, 0, null)
      return newState

    case REMOVE_STEP_DEPENDENCY:
      delete depth[index][action.index]
      depth[index] = depth[index].filter(d => d || d === null)
      return newState

    case UPDATE_STEP_DEPENDENCY:
      depth[index][action.index] = parseInt(action.value)
      return newState

    default:
      return newState
  }
}

export default reducer
