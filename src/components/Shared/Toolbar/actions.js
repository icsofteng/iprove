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

export const openDialog = (accept, callback) => {
  dialog({
    multiple: false,
    accept,
  }, (files) => {
    const reader = new FileReader()
    reader.readAsText(files[0])
    reader.onload = () => {
      callback(JSON.parse(reader.result))
    }
  })
}
