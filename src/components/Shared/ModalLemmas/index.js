import React, {Component} from 'react'
import styles from './styles.scss'
import TextBox from '../../Advanced/TextBox'


export default class ModalLemmas extends Component {
  render() {
    return <React.Fragment>
      <div className={styles.overlay} onClick={()=>this.props.onCancel()}></div>
      <div className={styles.panelBox}>
        <div className={styles.panelTitle}>Add a lemma</div>
          <div className={styles.panelContent}>
            {
              <TextBox
              key={"lemma"}
              ast= {{}}
              focus={true}
              z3={this.props.z3}
            />  
            }
          </div>
        </div>
    </React.Fragment>
  }

}