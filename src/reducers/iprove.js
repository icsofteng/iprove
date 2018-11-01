import _ from 'underscore'
import { scan_state } from '../utils'
import {
  NEW_RULE,
  NEW_STEP,
  REMOVE_RULE,
  CHANGE_SYMBOL,
  UPDATE_RULE,
  ADD_CONSTANTS,
  ADD_ATOMS,
  ADD_RELATIONS,
  ADD_STEP_DEPENDENCY,
  REMOVE_STEP_DEPENDENCY,
  UPDATE_STEP_DEPENDENCY,
  SET_STEP_DEPENDENCY,
  LOAD_PROOF,
  PUSH_SCOPE,
  POP_SCOPE
} from '../constants'

const initialState = {
  steps: [{ dependencies: [], ast: {}, scope: [] }],
  givens: [{ ast: {} }],
  goal: [{ ast: {} }],
  atoms: [],
  constants: [],
  relations: [],
  currentScope: []
}

const reducer = (state = initialState, action) => {
  let newState = JSON.parse(JSON.stringify(state))
  if (action.path) {
    const [key, ...path] = action.path
    const { depth, index } = scan_state(newState, path, key)

    switch (action.type) {
      case LOAD_PROOF:
        newState = {...newState, ...action.payload}
        return newState

      case NEW_STEP:
        depth[index] = { scope: newState.currentScope, dependencies: [], ast: { type: action.payload } }
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
        newState.constants = _.uniq(newConstants)
        return newState

      case ADD_ATOMS:
        const newAtoms = newState.atoms.concat(action.payload)
        newState.atoms = _.uniq(newAtoms)
        return newState

      case ADD_RELATIONS:
        const newRelations = newState.relations.concat(action.payload)
        newState.relations = _.uniq(newRelations, false, _.iteratee('name'))
        return newState

      case SET_STEP_DEPENDENCY:
        if (depth[index]) {
          depth[index] = action.payload.map(x => parseInt(x)).filter(x => !isNaN(x))
        }
        return newState

      case ADD_STEP_DEPENDENCY:
        depth[index] = depth[index] ? [...depth[index], null] : [null]
        return newState

      case REMOVE_STEP_DEPENDENCY:
        delete depth[index][action.index]
        depth[index] = depth[index].filter(d => d || d === null)
        return newState

      case UPDATE_STEP_DEPENDENCY:
        depth[index][action.index] = parseInt(action.value)
        return newState

      case PUSH_SCOPE:
        newState.currentScope.push(action.payload)
        newState.currentScope = _.uniq(newState.currentScope)
        return newState

      case POP_SCOPE:
        if (newState.currentScope[newState.currentScope.length - 1] === action.payload) {
          newState.currentScope.splice(-1, 1)
        }
        return newState

      default:
        return newState
    }
  }
  
  return newState
}

export default reducer
