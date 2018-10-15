import interact from 'interactjs'

export default class DragDrop {
  static onDrag(event) {
    var target = event.target,
        x = (parseFloat(target.getAttribute('data-x')) || 0) + event.dx,
        y = (parseFloat(target.getAttribute('data-y')) || 0) + event.dy;
  
    target.style.webkitTransform =
    target.style.transform =
      'translate(' + x + 'px, ' + y + 'px)';
  
    target.setAttribute('data-x', x);
    target.setAttribute('data-y', y);
  }

  static initialise() {
    interact('.dropzone').dropzone({
      accept: '.drag-drop',
      overlap: 0.75,
      ondragenter: function (event) {
        event.target.classList.add('drop-target')
        event.relatedTarget.classList.add('inside-target')
      },
      ondragleave: function (event) {
        event.target.classList.remove('drop-target')
        event.relatedTarget.classList.remove('inside-target')
      },
      ondrop: function (event) {
        console.log('add rule')
      },
    })
    
    interact('.drag-drop')
      .draggable({
        inertia: true,
        autoScroll: true,
        onmove: DragDrop.onDrag,
        onend: function (event) {
          if (!event.target.classList.contains('inside-target')) {
            console.log('reset')
          }
        }
      })
  }
}