import React from 'react'
import Rule from '../'
import SymbolChooser from '../SymbolChooser'
import RulePlaceholder from '../../RulePlaceholder'

const binSymbols = {
  and: '∧',
  or: '∨',
  implies: '⇒',
  iff: '⇔'
}

const BinaryRule = (props) =>
  <React.Fragment>
    { props.lhs ?
      <Rule
        updateValue={props.updateValue}
        deleteRule={props.deleteRule}
        addConstants={props.addConstants}
        path={[...props.path, "lhs"]}
        {...props.lhs}
      /> : <RulePlaceholder path={[...props.path, "lhs"]} dropLiteral={props.dropLiteral} />
    }
    <SymbolChooser
      updateValue={props.updateValue}
      current={props.symbol}
      path={[...props.path, "symbol"]}
      symbols={binSymbols}
    />
    { props.rhs ?
      <Rule
        updateValue={props.updateValue}
        deleteRule={props.deleteRule}
        addConstants={props.addConstants}
        path={[...props.path, "rhs"]}
        {...props.rhs}
      /> : <RulePlaceholder path={[...props.path, "rhs"]} dropLiteral={props.dropLiteral} />
    }
  </React.Fragment>

export default BinaryRule
