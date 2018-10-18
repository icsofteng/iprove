import React from 'react'

import Rule from '../'
import SymbolChooser from '../SymbolChooser'
import RulePlaceholder from '../../RulePlaceholder'

const UnaryRule = (props) =>
  <React.Fragment>
    <SymbolChooser
      changeSymbol={props.changeSymbol}
      current={props.symbol}
      path={props.path}
      symbols={unSymbols} />
    { props.value ?
      <Rule
        updateValue={props.updateValue}
        deleteRule={props.deleteRule}
        addConstant={props.addConstant}
        path={[...props.path, "value"]}
        {...props.value}
      /> :
      <RulePlaceholder
        path={[...props.path, "value"]}
      />
    }
  </React.Fragment>

const unSymbols = {
  not: '¬'
}

export default UnaryRule
