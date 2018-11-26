const express = require('express')
const app = express()
const bodyParser = require('body-parser')
const http = require('http')
const { exec, spawnSync } = require('child_process')
const fs = require('fs')
const { translate_and_save: translate_z3 } = require('./src/translator/z3')
const { translate_to_file: translate_latex } = require('./src/translator/latex')
const { parse } = require('./src/parser')
const { random_file_name } = require('./src/utils')

// Configuration
app.use(bodyParser.urlencoded({ extended: true }))
app.use(bodyParser.json())

app.use(express.static(__dirname + '/public'))

app.post('/z3', (req, res) => {
  const binary_file = process.platform === 'darwin' ? './z3-osx' : './z3'
  const { steps, identifiers, relations, types, functions } = req.body
  const file = translate_z3(steps, identifiers, relations, types, functions)

  exec(`${binary_file} ${file}`, (err, stdout) => {
    fs.unlink(file, () => res.send(stdout))
  })
})

app.get('/parse', (req, res) => {
  let { identifiers, relations, functions } = req.query
  res.send(parse(decodeURIComponent(req.query.input), JSON.parse(identifiers||"[]"), JSON.parse(relations||"[]"), JSON.parse(functions||"[]")))
})

app.post('/pdf', (req, res) => {
  const { steps, givens} = req.body
  const contents = translate_latex(givens, steps)
  const filename = random_file_name()
  fs.writeFileSync(filename, contents)
  spawnSync('xelatex', [filename], {stdio: 'ignore'})
  spawnSync('pdflatex', [filename], {stdio: 'ignore'})
  fs.unlinkSync(filename)
  fs.unlinkSync(filename + '.log')
  if (fs.existsSync(filename + '.aux')) {
    fs.unlinkSync(filename + '.aux')
  }
  if (fs.existsSync('texput.log')) {
    fs.unlinkSync('texput.log')
  }
  if (fs.existsSync(filename + '.pdf')) {
    const pdf = fs.readFileSync(filename + '.pdf')
    fs.unlinkSync(filename + '.pdf')
    res.send(pdf)
  }
  else {
    res.status(404).end()
  }
})

// Start server
const port = process.env.PORT || 8080
http.createServer(app).listen(port)
console.log('Listening on port ' + port)
