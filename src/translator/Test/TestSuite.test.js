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
/////
var test_constants = [{type: 'literal', value: 'p'}, {type: 'literal', value: 'q'}]

var test_rules = [{
    type: 'and',
    lhs: {
        type: 'literal',
        value: 'p'
    },
    rhs: {
        type: 'literal',
        value: 'q'
    },
},
{
    type: 'literal',
    value: 'p'
}]
/////

function checkFile(tmp, expected) {
    // console.log("expected dir is: " + expected + " " + fs.lstatSync(expected).isDirectory())
    const expectedContent = fs.readFileSync(expected).toString('utf-8')
    const actualContent = fs.readFileSync(tmp).toString('utf-8')
    return (expectedContent == actualContent)
}

function runTests(dir) {
    var dir = fs.readdirSync(dir)
    dir.forEach(testsFolder => {
        // console.log('In folder ' + testsFolder)
        var test_dir = dir + '/' + testsFolder
        console.log(test_dir)
        // require('./' + test_dir + '/UnTest')
        translate_to_SMT(test_rules, test_constants, true)
        console.log('TMP DIR: ' + test_dir + '/tmp.txt')
        if (checkFile(test_dir + '/tmp.txt', test_dir + '/expected.txt')) {
            // delete file
            console.log('ITS THE SAME')
        } else {
            console.log('Its not the same!')
        }
        // get test variables
        // run test with those variables
        // compare tmp file with expected.txt
        // expect(tmp file == expected).toBe(true) 
        // if it is not the same keep the file
        // if it is the same, delete and move on
    });
}

runTests("UnitTest/")
// runTests("IntegrationTest/")

// translate_to_SMT(test_rules, test_constants, false)


