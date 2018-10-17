const express = require('express')
const app = express()
const bodyParser = require('body-parser')
const http = require('http')
const { exec } = require('child_process')
const fs = require('fs')
const translator = require('./src/translator')

// Configuration
app.use(bodyParser.urlencoded({ extended: true }))
app.use(bodyParser.json())

app.use(express.static(__dirname + '/public'))

app.post('/z3', (req, res) => {
  const rules = req.params.rules
  const constants = req.params.constants
  const file = translator(rules, constants)
  const cmd = './z3 ' + file
  exec(cmd, (err, stdout) => {
    fs.unlink(file, () =>
      res.send(stdout)
    )
  })
})

// Start server
const port = process.env.PORT || 8080
http.createServer(app).listen(port)
console.log('Listening on port ' + port)