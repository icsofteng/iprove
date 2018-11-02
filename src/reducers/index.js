import undoable, { excludeAction } from 'redux-undo'
import iprove from './iprove'
import { ADD_CONSTANTS, ADD_ATOMS, ADD_RELATIONS } from '../constants';

export default undoable(iprove, {
  filter: excludeAction([ADD_CONSTANTS, ADD_ATOMS, ADD_RELATIONS])
})
