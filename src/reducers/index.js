import undoable, { excludeAction, groupByActionTypes } from 'redux-undo'
import iprove from './iprove'
import { ADD_IDENTIFIERS, ADD_ATOMS, ADD_RELATIONS, ADD_TYPES, UPDATE_RULE, SET_SCOPE, NEW_STEP } from '../constants';

export default undoable(iprove, {
  filter: excludeAction([ADD_IDENTIFIERS, ADD_ATOMS, ADD_RELATIONS, ADD_TYPES])
})
