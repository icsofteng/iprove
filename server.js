const express = require('express')
const app = express()
const bodyParser = require('body-parser')
const http = require('http')
const { exec } = require('child_process')
const fs = require('fs')
const { translate_and_save } = require('./src/translator/z3')
const { parse } = require('./src/parser')

// Configuration
app.use(bodyParser.urlencoded({ extended: true }))
app.use(bodyParser.json())

app.use(express.static(__dirname + '/public'))

app.post('/z3', (req, res) => {
  const steps = req.body.steps
  const constants = req.body.constants
  const file = translate_and_save(steps, constants)
  const cmd = './z3 ' + file
  exec(cmd, (err, stdout) => {
    fs.unlink(file, () =>
      res.send(stdout)
    )
  })
})

app.get('/parse', (req, res) => {
  res.send(parse(req.query.input))
})

// Start server
const port = process.env.PORT || 8080
http.createServer(app).listen(port)
console.log('Listening on port ' + port)