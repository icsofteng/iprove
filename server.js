const express = require('express')
const app = express()
const bodyParser = require('body-parser')
const http = require('http')
const { exec } = require('child_process')
const fs = require('fs')

// Configuration
app.use(bodyParser.urlencoded({ extended: true }))
app.use(bodyParser.json())

app.use(express.static(__dirname + '/public'))

app.get('/z3', (req, res) => {
  const code = req.query.code
  fs.writeFile("tmp", code, () => {
    const cmd = './z3 tmp'
    exec(cmd, (err, stdout) => {
      fs.unlink('tmp', () =>
        res.send(stdout)
      )
    })
  })
})

// Start server
const port = process.env.PORT || 8080
http.createServer(app).listen(port)
console.log('Listening on port ' + port)