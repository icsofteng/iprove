import undoable, { excludeAction } from 'redux-undo'
import iprove from './iprove'
import { ADD_IDENTIFIERS, ADD_ATOMS, ADD_RELATIONS, ADD_TYPES, NEW_STEP } from '../constants';

export default undoable(iprove, {
  filter: excludeAction([ADD_IDENTIFIERS, ADD_ATOMS, ADD_RELATIONS, ADD_TYPES, NEW_STEP])
})
