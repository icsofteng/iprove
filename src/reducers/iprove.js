import { scan_state } from '../utils'
import { SET_SELECTED, UPDATE_DEP_KEY_DOWN, UPDATE_DEP_NOTHING, ENABLE_EDIT, PARSE_KEY_DOWN, PARSE_NOTHING } from '../constants'
import { setSelected, updateDepKeyDown, updateDepNothing, enableEdit, parseKeyDown, parseNothing } from './actions'

const initialState = {
  steps: [{ dependencies: [], ast: {}, scope: [], edit: true }],
  givens: [{ ast: {}, edit: true }],
  goal: [{ ast: {}, edit: true }],
  identifiers: [],
  relations: [],
  functions: [],
  types: [],
  goalAchieved: [],
  z3: [],
  simple: false,
  selectedTextBox: ["givens", 0, false],
}

const reducer = (state = initialState, { type, path = [], payload, ...otherArgs }) => {
  let newState = JSON.parse(JSON.stringify(state))
  const [key, ...extractedPath] = path
  let { depth, scanIndex } = scan_state(newState, extractedPath, key)
  switch (type) {
    case SET_SELECTED: setSelected(newState, payload); return newState
    case UPDATE_DEP_KEY_DOWN: updateDepKeyDown(newState, payload); return newState
    case UPDATE_DEP_NOTHING: updateDepNothing(newState, payload); return newState
    case ENABLE_EDIT: enableEdit(newState, depth[scanIndex], path); return newState
    case PARSE_KEY_DOWN: parseKeyDown(newState, payload, otherArgs.keyCode); return newState
    case PARSE_NOTHING: parseNothing(newState, payload); return newState
    default: return newState
  }
}

export default reducer
