export const setSelected = (state, selected) => {
  state.selectedTextBox = selected
}

export const enableEdit = (state, step, path) => {
  step.edit = true
  setSelected(state, [...path, false])
}

export const updateDepKeyDown = (state, dependencies) => {
  const [section, line] = state.selectedTextBox
  const currentScope = state[section][line].scope
  updateDepNothing(state, dependencies)
  state[section].splice(line+1, 0, { scope: currentScope, dependencies: [], ast: {}, edit: true })
  setSelected(state, [section, line+1, false])
}

export const updateDepNothing = (state, dependencies) => {
  const [section, line] = state.selectedTextBox
  state[section][line].dependencies = dependencies.split(/[\s,]+/)
  setSelected(state, ['', -1, false])
}

export const parseNothing = (state, response) => {
  const [section, line] = state.selectedTextBox
  const { ast, identifiers, relations, types, functions, errors } = response
  if (ast[0].type === 'exit') {
    state[section][line].scope = state[section][line].scope.slice(0, -1)
  }
  else {
    state.identifiers = identifiers
    state.relations = relations
    state.types = types
    state.functions = functions
    state.errors = errors
    state[section][line].ast = ast[0]
    if (ast[0].type === 'assume' || ast[0].type === 'case') {
      state[section][line].scope = [...state[section][line], line]
    }
    state[section][line].edit = false
  }
  setSelected(state, ['', -1, false])
}

export const parseKeyDown = (state, response, keyCode) => {
  const [section, line] = state.selectedTextBox
  parseNothing(state, response)
  if (keyCode === 9) {
    // TAB
    setSelected(state, [section, line, true])
    if (section === 'givens') {
      keyCode = 13
    }
  }
  if (keyCode === 13) {
    // ENTER
    const currentScope = state[section][line].scope
    state[section].splice(line+1, 0, { scope: currentScope, dependencies: [], ast: {}, edit: true })
    setSelected(state, [section, line+1, false])
  }
}

// case LOAD_PROOF:
//       newState = {...newState, ...payload}
//       return newState

//     case NEW_STEP:
//       let scope = (key === 'steps') ? depth[scanIndex - 1].scope : []
//       depth.splice(scanIndex, 0, { scope, dependencies: [], ast: { type: payload, ...otherArgs } })
//       return newState

//     case REMOVE_STEP:
//       if (Array.isArray(depth)) {
//         depth.splice(scanIndex, 1)
//       }
//       else {
//         delete depth[scanIndex]
//       }
//       return { ...newState, steps: newState.steps.filter(Boolean) }

//     case NEW_RULE:
//       depth[scanIndex] = { type: payload, ...otherArgs }
//       return newState

//     case UPDATE_RULE:
//       depth[scanIndex] = payload
//       return newState

//     case REMOVE_RULE:
//       if (Array.isArray(depth)) {
//         depth.splice(scanIndex, 1)
//       }
//       else {
//         delete depth[scanIndex]
//       }
//       return { ...newState, steps: newState.steps.filter(Boolean)}

//     case CHANGE_SYMBOL:
//       depth[scanIndex].symbol = payload
//       return newState

//     case ADD_IDENTIFIERS:
//       const newConstants = newState.identifiers.concat(payload)
//       newState.identifiers = _.uniq(newConstants, false, _.iteratee('value'))
//       return newState

//     case ADD_ATOMS:
//       const newAtoms = newState.atoms.concat(payload)
//       newState.atoms = _.uniq(newAtoms)
//       return newState

//     case ADD_RELATIONS:
//       const newRelations = newState.relations.concat(payload)
//       newState.relations = _.uniq(newRelations, false, _.iteratee('name'))
//       return newState

//     case ADD_FUNCTIONS:
//       const newFunctions = newState.functions.concat(payload)
//       newState.functions = _.uniq(newFunctions, false, _.iteratee('name'))
//       return newState

//     case ADD_TYPES:
//       const newTypes = newState.types.concat(payload)
//       newState.types = _.uniq(newTypes)
//       return newState

//     case SET_STEP_DEPENDENCY:
//       if (depth[scanIndex]) {
//         depth[scanIndex] = payload
//       }
//       return newState

//     case ADD_STEP_DEPENDENCY:
//       depth[scanIndex] = depth[scanIndex] ? [...depth[scanIndex], null] : [null]
//       return newState

//     case REMOVE_STEP_DEPENDENCY:
//       delete depth[scanIndex][otherArgs.index]
//       depth[scanIndex] = depth[scanIndex].filter(d => d || d === null)
//       return newState

//     case UPDATE_STEP_DEPENDENCY:
//       depth[scanIndex][otherArgs.index] = otherArgs.value
//       return newState

//     case SET_SCOPE:
//       depth[scanIndex].scope = _.uniq(payload)
//       if (otherArgs.removeLine) {
//         depth[scanIndex] = { dependencies: [], ast: {}, scope: depth[scanIndex].scope }
//       }
//       return newState

//     case CLEAR_PROOF:
//       newState = { ...newState, steps: [{ dependencies: [], ast: {}, scope: [] }] }
//       return newState

//     case ADD_CASE:
//       let startScope = newState.steps[otherArgs.start-newState.givens.length-1].scope
//       let newIndex = otherArgs.end-newState.givens.length
//       newState.steps.splice(newIndex, 0, { scope: [...startScope, newIndex], dependencies: [], ast: { type: 'assume' } })
//       return newState

//     case BEAUTIFY:
//       const prevSteps = newState.steps
//       prevSteps.pop()
//       const lastStep = payload
//       newState = { ...newState, steps: [...prevSteps, lastStep]}
//       return newState

//     case UPDATE_Z3:
//       newState.z3 = payload
//       return newState

//     case SET_GOAL_ACHIEVED:
//       newState.goalAchieved = payload
//       return newState

//     case SET_SELECTED:
//       newState.selectedTextBox = payload
//       return newState

//     case SWITCH_MODE:
//       newState.simple = !newState.simple
//       return newState