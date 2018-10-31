import React from 'react'

import Rule from '../../'
import RulePlaceholder from '../../../RulePlaceholder'

const Relation = (props) => (
  <React.Fragment>
    { props.name }
    ({ props.params.map((param, index) => (
      param ?
        <Rule
          updateValue={props.updateValue}
          deleteRule={props.deleteRule}
          addConstants={props.addConstants}
          path={[...props.path, "params", index]}
          key={`param-rule${index}`}
          {...param}
        />
        :
        <RulePlaceholder
          path={[...props.path, "params", index]}
          dropLiteral={props.dropLiteral}
          key={`param-placeholder${index}`}
        />
    ))})
  </React.Fragment>
)

export default Relation
