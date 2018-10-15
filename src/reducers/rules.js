import { NEW_RULE, REMOVE_RULE, CHANGE_FOCUS, UPDATE_RULE, CLICK_SYMBOL } from '../constants'

const initialState = {
  focus: 0,
  steps: ['']
}

const rules = (state = initialState, action) => {
  const steps = state.steps.slice(0)
  switch (action.type) {
    case NEW_RULE:
      return {
        ...state,
        steps: [...state.steps, '']
      }

    case REMOVE_RULE:
      if (state.steps.length <= 1) {
        return state
      }
      steps.splice(action.payload, 1)
      return {
        ...state,
        steps,
        focus: (state.focus === action.payload ? 0 : state.focus)
      }

    case CHANGE_FOCUS:
      return {
        ...state,
        focus: action.payload
      }
    
    case CLICK_SYMBOL:
      steps[state.focus] += action.payload
      return {
        ...state,
        steps
      }

    case UPDATE_RULE:
      steps[state.focus] = action.payload
      return {
        ...state,
        steps
      } 

    default:
      return state
  }
}

export default rules
