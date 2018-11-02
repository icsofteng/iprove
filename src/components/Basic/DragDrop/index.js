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
        const { type, symbol } = event.relatedTarget.dataset

        let otherArgs = {}

        if (type === 'relation') {

        }

        switch (type) {
          case 'relation':
            otherArgs = { params: [] }
            break;
          case 'universal_quantifier':
            otherArgs = { symbol: 'forall' }
            break
          case 'existential_quantifier':
            otherArgs = { symbol: 'exists' }
            break
          default: break
        }

        if (Array.from(event.target.classList).indexOf("wide") > -1) {
          this.props.addStep(type, symbol, JSON.parse(event.target.dataset.path), otherArgs)
        }
        else {
          this.props.addRule(type, symbol, JSON.parse(event.target.dataset.path), otherArgs)
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
    addStep: (type, symbol, path, otherArgs) => dispatch({ type: NEW_STEP, payload: type, symbol, path, otherArgs }),
    addRule: (type, symbol, path, otherArgs) => dispatch({ type: NEW_RULE, payload: type, symbol, path, otherArgs })
  }
}

export default connect(null, mapDispatchToProps)(DragDrop)
