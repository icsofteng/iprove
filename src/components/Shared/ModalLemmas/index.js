import React, {Component} from 'react'
import styles from './styles.scss'
import TextBoxList from '../../Advanced/TextBoxList'


export default class ModalLemmas extends Component {
  render() {
    return ([
      <div className={styles.overlay} onClick={()=>this.props.onCancel()}></div>,
      <div className={styles.panelBox}>
        <div className={styles.panelTitle}>Lemmas</div>
          <div className={styles.panelContent}>
            {
              <TextBoxList z3={this.props.z3} start={0} steps={this.props.steps} type="lemmas" selectedTextBox={this.props.selectedTextBox} setSelected={this.props.setSelected} incrementInput={this.props.incrementInput} newStepAfter={this.props.newStepAfter} removeCurrentStep={this.props.removeCurrentStep} />
            }
          </div>
        </div>
    ]);
  }

}