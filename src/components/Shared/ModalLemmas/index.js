import React, {Component} from 'react';

export default class ModalLemmas extends Component {
  render() {
    return ([
      <div key="modal-overlay" className="modal-overlay" onClick={()=>this.props.onCancel()}/>,

    ]);
  }

}