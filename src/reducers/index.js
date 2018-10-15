import { NEW_RULE, REMOVE_RULE, UPDATE_RULE, UPDATE_RULE_LHS, UPDATE_RULE_RHS, CHANGE_SYMBOL} from '../constants'

const initialState = {
  steps: []
}

const reducer = (state = initialState, action) => {
  const newState = Object.assign({}, state)
  newState.steps = state.steps.slice(0)
  switch (action.type) {
    case NEW_RULE:
      return { ...newState, steps: [...newState.steps, { type: action.payload }] }

    case REMOVE_RULE:
      newState.steps.splice(action.payload, 1)
      return newState

    case UPDATE_RULE:
      newState.steps[action.index].value = action.payload
      return newState

    case UPDATE_RULE_LHS:
      newState.steps[action.index].lhs = action.payload
      return newState

    case UPDATE_RULE_RHS:
      newState.steps[action.index].rhs = action.payload
      return newState

    case CHANGE_SYMBOL:
      newState.steps[action.index].symbol = action.payload
      return newState

    default:
      return newState
  }
}

export default reducer
