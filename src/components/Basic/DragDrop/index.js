import React, { Component } from 'react'
import { connect } from 'react-redux'
import interact from 'interactjs'
import { NEW_RULE, NEW_STEP } from '../../../constants'

class DragDrop extends Component {
  componentDidMount() {
    this.initialise()
  }

  onDrag(event) {
    var target = event.target,
        x = (parseFloat(target.getAttribute('data-x')) || 0) + event.dx,
        y = (parseFloat(target.getAttribute('data-y')) || 0) + event.dy;
  
    target.style.webkitTransform =
    target.style.transform =
      'translate(' + x + 'px, ' + y + 'px)';
  
    target.setAttribute('data-x', x);
    target.setAttribute('data-y', y);
  }

  initialise() {
    interact('.dropzone').dropzone({
      accept: '.drag-drop',
      ondragenter: function (event) {
        event.target.classList.add('drop-target')
        event.relatedTarget.classList.add('inside-target')
      },
      ondragleave: function (event) {
        event.target.classList.remove('drop-target')
        event.relatedTarget.classList.remove('inside-target')
      },
      ondrop: function (event) {
        event.target.classList.remove('drop-target')
        if (Array.from(event.target.classList).indexOf("wide") > -1) {
          this.props.addStep(event.relatedTarget.dataset.type, JSON.parse(event.target.dataset.path))
        }
        else {
          this.props.addRule(event.relatedTarget.dataset.type, JSON.parse(event.target.dataset.path))
        }
      }.bind(this),
    })
    
    interact('.drag-drop')
      .draggable({
        inertia: true,
        autoScroll: true,
        onmove: this.onDrag,
        onend: function (event) {
          event.target.style.webkitTransform =
          event.target.style.transform = 'translate(' + 0 + 'px, ' + 0 + 'px)'
          event.target.setAttribute('data-x', 0);
          event.target.setAttribute('data-y', 0);
        }
      })
  }

  render() {
    return null
  }
}

const mapDispatchToProps = dispatch => {
  return {
    addStep: (type, path) => dispatch({ type: NEW_STEP, payload: type, path }),
    addRule: (type, path) => dispatch({ type: NEW_RULE, payload: type, path })
  }
}

export default connect(null, mapDispatchToProps)(DragDrop)