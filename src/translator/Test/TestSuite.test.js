// import translate_to_SMT from '../SMT_translator'
//import the SMT translator function
// Function:
//      For each folders in the name directory
//          get the test_constants and test_rules
//          Run translate with those 2 var
//          Compare the file generated with the expected.txt in the folder
//          if it is not the same keep the file
//          if it is the same, delete and move on

// Unit runs all the folders in unit test
// Integration runs all the folders in Integration
// checkFile(tmp, expected)


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


