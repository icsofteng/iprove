import React from 'react'
import cx from 'classnames'

import Rule from '../../'
import RulePlaceholder from '../../../RulePlaceholder'

import styles from './styles.scss'

const symbols = {
  universal_quantifier: '∀',
  existential_quantifier: '∃',
}

const Quantifier = (props) => (
  <React.Fragment>
    <span className={cx(styles.quantifierSymbol)}>
      { symbols[props.type] }
    </span>
    { props.variable ?
      <Rule
        updateValue={props.updateValue}
        deleteRule={props.deleteRule}
        addIdentifiers={props.addIdentifiers}
        path={[...props.path, "variable"]}
        {...props.variable}
      /> : <RulePlaceholder path={[...props.path, "variable"]} dropLiteral={props.dropLiteral} />
    }
    { props.value ?
      <Rule
        updateValue={props.updateValue}
        deleteRule={props.deleteRule}
        addIdentifiers={props.addIdentifiers}
        path={[...props.path, "value"]}
        {...props.value}
      /> : <RulePlaceholder path={[...props.path, "value"]} dropLiteral={props.dropLiteral} />
    }
  </React.Fragment>
)

export default Quantifier
