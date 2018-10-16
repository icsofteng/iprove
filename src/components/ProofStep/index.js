import React from 'react'
import { connect } from 'react-redux'
import Rule from '../Rule'
import styles from './styles.scss'

const ProofStep = (props) =>
  <div className={styles.steps}>
    <h1>{props.index}</h1>
    <Rule key={"rule"+props.index} {...props.rule} path={[props.index]} />
  </div>

const mapStateToProps = () => {
  return { }
}

export default connect(mapStateToProps, null)(ProofStep)