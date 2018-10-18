import React from 'react'

import Rule from '../'
import SymbolChooser from '../SymbolChooser'
import RulePlaceholder from '../../RulePlaceholder'

const unSymbols = {
  not: '¬'
}

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
        {...props.value}
      /> :
      <RulePlaceholder
        path={[...props.path, "value"]}
      />
    }
  </React.Fragment>

export default UnaryRule
