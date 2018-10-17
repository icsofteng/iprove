const translate = require('../')
const fs = require('fs')

const check_file = (tmp, expected) => {
  const expectedContent = fs.readFileSync(expected).toString('utf-8')
  const actualContent = fs.readFileSync(tmp).toString('utf-8')
  return (expectedContent === actualContent)
}

const root = 'src/translator/test/'

const run_tests = (dir) => {
  var folders = fs.readdirSync(root + dir)
  folders.forEach(tests_folder => {
    const test_dir = root + dir + tests_folder
    const test_file = require('./'+ dir + tests_folder + '/Test')
    const tmp_file = translate(test_file.test_rules, test_file.test_constants)
    const result = check_file('./' + tmp_file, test_dir + '/expected.txt')
    test(tests_folder, () => {
      expect(result).toEqual(true)
    })
    fs.unlinkSync(tmp_file)
  });
}

run_tests("UnitTest/")
run_tests("IntegrationTest/")