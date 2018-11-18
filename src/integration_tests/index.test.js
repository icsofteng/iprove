import fs from 'fs'
import glob from 'glob-fs'
import React from 'react'
import IProve from '../components'
import { createMockStore } from 'redux-test-utils'
import { shallowWithStore } from 'enzyme-redux'
import { execSync } from 'child_process'
import { translate_and_save } from '../translator/z3'

global.fetch = (url, options) => {
  return new Promise((resolve, reject) => {
    const body = JSON.parse(options.body)
    const { steps, atoms, constants, relations, types } = body
    const file = translate_and_save(steps, constants, relations, atoms, types)
    const result = execSync(`./z3-deb ${file}`)
    fs.unlink(file, () =>
      resolve({
        text: () => Promise.resolve(result.toString('utf8'))
      })
    )
  })
}

const integration_test = (f) => {
  return new Promise((res, rej) => {
    const { props } = JSON.parse(fs.readFileSync(f))
    const store = createMockStore({ present: props })
    const component = shallowWithStore(<IProve />, store).dive()
    component.setState({ goalAchieved: [], "z3": [], "simple": false, "selectedTextBox": ["",-1] })
    component.instance().getRequiredSteps().then(() => {
      const z3s = component.state().z3
      z3s.forEach((z3) => expect(z3).toEqual('unsat'))
      res()
    })
  })
}

test('Integration tests', (done) => {
  const files = glob().readdirSync('**/*.proof')
  const run_tests = files.map(f => integration_test(f))
  Promise.all(run_tests).then(() => done())
})