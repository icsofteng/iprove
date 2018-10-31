import React from 'react'

import Rule from '../../'
import RulePlaceholder from '../../../RulePlaceholder'

const symbols = {
  forall: '∀',
  exists: '∃',
}

const Quantifier = (props) => (
  <React.Fragment>
    { symbols[props.symbol] ? symbols[props.symbol] : '' }
    { props.variable ?
      <Rule
        updateValue={props.updateValue}
        deleteRule={props.deleteRule}
        addConstants={props.addConstants}
        path={[...props.path, "variable"]}
        {...props.variable}
      /> : <RulePlaceholder path={[...props.path, "variable"]} dropLiteral={props.dropLiteral} />
    }
    { props.value ?
      <Rule
        updateValue={props.updateValue}
        deleteRule={props.deleteRule}
        addConstants={props.addConstants}
        path={[...props.path, "value"]}
        {...props.value}
      /> : <RulePlaceholder path={[...props.path, "value"]} dropLiteral={props.dropLiteral} />
    }
  </React.Fragment>
)

export default Quantifier
