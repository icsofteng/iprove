import _ from 'underscore'
import { scan_state } from '../utils'
import {
  NEW_RULE,
  REMOVE_STEP,
  NEW_STEP,
  REMOVE_RULE,
  CHANGE_SYMBOL,
  UPDATE_RULE,
  ADD_IDENTIFIERS,
  ADD_ATOMS,
  ADD_RELATIONS,
  ADD_FUNCTIONS,
  ADD_STEP_DEPENDENCY,
  REMOVE_STEP_DEPENDENCY,
  UPDATE_STEP_DEPENDENCY,
  SET_STEP_DEPENDENCY,
  LOAD_PROOF,
  SET_SCOPE,
  ADD_TYPES,
  CLEAR_PROOF,
  ADD_CASE,
  BEAUTIFY,
  ADD_LEMMAS,
  SET_Z3,
  SET_GOAL_ACHIEVED,
  SET_SELECTED
} from '../constants'

const initialState = {
  steps: [{ dependencies: [], ast: {}, scope: [], raw: '', errors: false, placeholder: 'Start your proof here' }],
  givens: [{ ast: {}, raw: '', errors: false, placeholder: 'Type something that\'s always true' }],
  goal: [{ ast: {}, raw: '', errors: false, placeholder: 'What do you want to prove?' }],
  identifiers: [],
  relations: [],
  functions: [],
  types: [],
  lemmas: [],
  z3: [],
  goalAchieved: [],
  selectedTextBox: ["givens", 0]
}

const reducer = (state = initialState, action) => {
  let newState = JSON.parse(JSON.stringify(state))
  if (action.path) {
    const [key, ...path] = action.path
    let { depth, index } = scan_state(newState, path, key)
    switch (action.type) {
      case SET_SELECTED:
        newState.selectedTextBox = action.payload
        return newState

      case SET_GOAL_ACHIEVED:
        newState.goalAchieved = action.payload
        return newState

      case SET_Z3:
        newState.z3 = action.payload
        return newState

      case LOAD_PROOF:
        newState = {...newState, ...action.payload}
        return newState

      case NEW_STEP:
        let scope = (key === 'steps') ? depth[index - 1].scope : []
        depth.splice(index, 0, { scope, dependencies: [], ast: { type: action.payload, ...action.otherArgs } })
        return newState

      case REMOVE_STEP:
        if (Array.isArray(depth)) {
          depth.splice(index, 1)
        }
        else {
          delete depth[index]
        }
        return { ...newState, steps: newState.steps.filter(Boolean) }

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
        return { ...newState, steps: newState.steps.filter(Boolean)}

      case CHANGE_SYMBOL:
        depth[index].symbol = action.payload
        return newState

      case ADD_IDENTIFIERS:
        // concat old identifiers onto new ones, uniq then finds new ones first 
        // and discards old definitions if e.g. type has changed of a declared identifier
        const newConstants = action.payload.concat(newState.identifiers)
        newState.identifiers = _.uniq(newConstants, false, _.iteratee('value'))
        return newState

      case ADD_ATOMS:
        const newAtoms = newState.atoms.concat(action.payload)
        newState.atoms = _.uniq(newAtoms)
        return newState

      case ADD_RELATIONS:
        const newRelations = newState.relations.concat(action.payload)
        newState.relations = _.uniq(newRelations, false, ({name, params}) => {
          return JSON.stringify({name, params})
        })
        return newState

      case ADD_FUNCTIONS:
        const newFunctions = newState.functions.concat(action.payload)
        newState.functions = _.uniq(newFunctions, false, _.iteratee('name'))
        return newState

      case ADD_TYPES:
        const newTypes = newState.types.concat(action.payload)
        newState.types = _.uniq(newTypes)
        return newState

      case SET_STEP_DEPENDENCY:
        if (depth[index]) {
          depth[index] = action.payload
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
        depth[index][action.index] = action.value
        return newState

      case SET_SCOPE:
        depth[index].scope = _.uniq(action.payload)
        if (action.removeLine) {
          depth[index] = { dependencies: [], ast: {}, scope: depth[index].scope }
        }
        return newState

      case CLEAR_PROOF:
        newState = { ...newState, steps: [{ dependencies: [], ast: {}, scope: [] }] }
        return newState

      case ADD_CASE:
        let startScope = newState.steps[action.start-newState.givens.length-1].scope
        let newIndex = action.end-newState.givens.length
        newState.steps.splice(newIndex, 0, { scope: [...startScope, newIndex], dependencies: [], ast: { type: 'assume' } })
        return newState

      case BEAUTIFY:
        const prevSteps = newState.steps
        prevSteps.pop()
        const lastStep = action.payload
        newState = { ...newState, steps: [...prevSteps, lastStep]}
        return newState

      case ADD_LEMMAS:
        const newLemmas = newState.lemmas.concat(action.payload)
        newState.lemmas = _.uniq(newLemmas)
        return newState

      default:
        return newState
    }
  }

  return newState
}

export default reducer
