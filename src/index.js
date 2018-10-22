import React from 'react'
import { render } from 'react-dom'
import { Provider } from 'react-redux'
import { createStore } from 'redux'
import reducer from './reducers'
import IProve from './components/IProve'

const store = createStore(reducer)

render(
  <Provider store={store}>
    <IProve />
  </Provider>,
  document.getElementById('root')
)