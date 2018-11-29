import save from 'save-file'
import dialog from 'open-file-dialog'

export const saveDialog = (data, name) => {
  save(JSON.stringify(data), name, (err, data) => {
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
