import React, {Component} from 'react'
import styles from './styles.scss'
import TextBoxList from '../../Advanced/TextBoxList'


export default class ModalLemmas extends Component {
  render() {
    return ([
      <div className={styles.overlay} onClick={()=>this.props.onCancel()}>
        <div className={styles.panelBox}>
          <div className={styles.panelTitle}>Givens</div>
            <div className={styles.panelContent}>
              {
                <TextBoxList z3={this.state.z3} start={0} steps={this.props.givens} type="givens" selectedTextBox={this.state.selectedTextBox} setSelected={this.setSelected} incrementInput={this.incrementInput} newStepAfter={this.newStepAfter} removeCurrentStep={this.removeCurrentStep} />
              }
            </div>
          </div>
        </div>

    ]);
  }

}