const translate_to_SMT = require('../SMT_translator.js')
var fs = require('fs')

function checkFile(tmp, expected) {
  const expectedContent = fs.readFileSync(expected).toString('utf-8')
  const actualContent = fs.readFileSync(tmp).toString('utf-8')
  return (expectedContent == actualContent)
}

const root = 'src/translator/Test/'

function runTests(dir){
  var folders = fs.readdirSync( root + dir )
  folders.forEach(tests_folder => {
    const test_dir = root + dir + tests_folder
    const test_tmp = test_dir + '/tmp.txt'
    const test_dir_obj = './'+ test_dir + '/Test'
    const obj = require('./'+ dir + tests_folder + '/Test')
    translate_to_SMT(obj.test_rules, obj.test_constants, test_tmp)
    const result = checkFile(test_tmp, test_dir + '/expected.txt')
    test(tests_folder, ()=> {
      expect(result).toBe(true)
    })
    if (result) {
      fs.unlinkSync(test_tmp)
    }
  });
}

runTests("UnitTest/")

runTests("IntegrationTest/")


