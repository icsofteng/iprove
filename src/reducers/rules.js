import { NEW_RULE, REMOVE_RULE } from '../constants'

const initialState = {
  steps: []
}

const rules = (state = initialState, action) => {
  const steps = state.steps.slice(0)
  switch (action.type) {
    case NEW_RULE:
      return {
        ...state,
        steps: [...state.steps, { type: action.payload }]
      }

    case REMOVE_RULE:
      if (state.steps.length <= 1) {
        return state
      }
      steps.splice(action.payload, 1)
      return {
        ...state,
        steps
    }

    default:
      return state
  }
}

export default rules
