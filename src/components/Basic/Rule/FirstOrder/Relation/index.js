import React, { Component } from 'react'
import cx from 'classnames'

import Rule from '../../'
import RulePlaceholder from '../../../RulePlaceholder'

import styles from '../../styles.scss'

class Relation extends Component {
  render() {
    const last_param_index = this.props.params ? this.props.params.length : 0

    return (
      <React.Fragment>
        <input
          type="text"
          value={this.props.name}
          onChange={(event) => {
            this.props.updateValue([...this.props.path, "name"], event.target.value)
          }}
          className={cx(styles.wideRuleInput)}
          ref={(ref) => this.ref = ref}
        />
        ({ this.props.params && this.props.params.map((param, index) => (
          <Rule
            updateValue={this.props.updateValue}
            deleteRule={this.props.deleteRule}
            addConstants={this.props.addConstants}
            path={[...this.props.path, "params", index]}
            key={`param-rule${index}-${last_param_index}`}
            {...param}
          />
        ))}
        <RulePlaceholder
          path={[...this.props.path, "params", last_param_index]}
          dropLiteral={this.props.dropLiteral}
          key={`param-rule${last_param_index}-${last_param_index}`}
        />
        )
      </React.Fragment>
    )
  }
}

export default Relation
