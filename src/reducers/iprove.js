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
  SET_SCOPE,
  ADD_TYPES,
  OPEN_CASE
} from '../constants'

const initialState = {
  steps: [{ dependencies: [], ast: {}, scope: [] }],
  givens: [{ ast: {} }],
  goal: [{ ast: {} }],
  atoms: [],
  constants: [],
  relations: [],
  currentScope: [],
  types: []
}

const reducer = (state = initialState, action) => {
  let newState = JSON.parse(JSON.stringify(state))
  if (action.path) {
    const [key, ...path] = action.path
    let { depth, index } = scan_state(newState, path, key)

    switch (action.type) {
      case LOAD_PROOF:
        newState = {...newState, ...action.payload}
        return newState

      case NEW_STEP:
        let scope = (key === 'steps') ? newState.currentScope : []
        depth[index] = { scope, dependencies: [], ast: { type: action.payload, ...action.otherArgs } }
        return newState

      case NEW_RULE:
        depth[index] = { type: action.payload, ...action.otherArgs }
        return newState

      case UPDATE_RULE:
        depth[index] = action.payload
        return newState

      case REMOVE_RULE:
        if (Array.isArray(depth)) {
          depth.splice(index, 1)
        }
        else {
          delete depth[index]
        }
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

      case ADD_TYPES:
        const newTypes = newState.types.concat(action.payload)
        newState.types = _.uniq(newTypes)
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

      case SET_SCOPE:
        if (action.override) {
          // This is an "assume" line
          newState.currentScope = [...action.payload, action.thisIndex]
          newState.currentScope = _.uniq(newState.currentScope)
          newState.steps[action.thisIndex].scope = newState.currentScope
        }
        else {
          // This is an "exit" line
          newState.currentScope = action.payload
          newState.currentScope = _.uniq(newState.currentScope)
          if (newState.steps[action.thisIndex].ast.type === 'exit') {
            newState.steps.splice(action.thisIndex, 1)
          }
        }
        return newState

      case OPEN_CASE:
        const originalScope = newState.currentScope
        newState.currentScope = [...originalScope, newState.steps.length]
        newState.currentScope = _.uniq(newState.currentScope)
        newState.steps.push({ scope: newState.currentScope, dependencies: [], ast: { type: undefined } })
        newState.currentScope = [...originalScope, newState.steps.length]
        newState.currentScope = _.uniq(newState.currentScope)
        newState.steps.push({ scope: newState.currentScope, dependencies: [], ast: { type: undefined } })
        newState.currentScope = originalScope
        newState.steps.push({ scope: newState.currentScope, dependencies: [], ast: { type: undefined } })
        return newState

      default:
        return newState
    }
  }
  
  return newState
}

export default reducer
