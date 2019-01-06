import undoable, { combineFilters, excludeAction } from 'redux-undo'
import iprove from './iprove'
import { ADD_IDENTIFIERS, ADD_ATOMS, ADD_RELATIONS, ADD_TYPES, SET_SELECTED, SET_GOAL_ACHIEVED, ADD_FUNCTIONS, TOGGLE_SECTION, UPDATE_RULE } from '../constants';

export default undoable(iprove, {
  debug: true,
  filter: combineFilters(
    excludeAction([ADD_IDENTIFIERS, ADD_ATOMS, ADD_RELATIONS, ADD_FUNCTIONS, ADD_TYPES, SET_SELECTED, SET_GOAL_ACHIEVED, TOGGLE_SECTION]),
    (action) => action.type !== UPDATE_RULE || (action.type === UPDATE_RULE && action.path.slice(-1)[0] === "raw")
  )
})
