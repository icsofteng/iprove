import save from 'save-file'
import dialog from 'open-file-dialog'

export const saveDialog = (props, state) => {
  const data = JSON.stringify({ props, state })
  const d = new Date()
  const date = d.getDate().toString() + (d.getMonth()+1).toString() + d.getFullYear().toString()
  save(data, date + '.proof', (err, data) => {
    console.log("File saved")
  })
}

export const openDialog = (callback) => {
  dialog({
    multiple: false,
    accept: '.proof'
  }, (files) => {
    const reader = new FileReader()
    reader.readAsText(files[0])
    reader.onload = () => {
      const { props, state } = JSON.parse(reader.result)
      callback(props, state)
    }
  })
}