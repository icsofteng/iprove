import fs from 'fs'
import glob from 'glob-fs'
import React from 'react'
import IProve from '../components'
import { createMockStore } from 'redux-test-utils'
import { shallowWithStore } from 'enzyme-redux'
import { exec } from 'child_process'
import { translate_and_save } from '../translator/z3'
import TextBoxList from '../components/Advanced/TextBoxList'
import TextBox from '../components/Advanced/TextBox'

global.fetch = (_, options) => {
  return new Promise((resolve, _) => {
    const body = JSON.parse(options.body)
    const { steps, identifiers, relations, types, functions } = body
    const file = translate_and_save(steps, identifiers, relations, types, functions)
    const binary_file = process.env.SERVER === 'test' ? './z3-deb' : (process.platform === 'darwin' ? './z3-osx' : './z3')
    exec(`${binary_file} ${file}`, (err, stdout) => {
      fs.unlink(file, () =>
        resolve({
          text: () => Promise.resolve(stdout.toString('utf8'))
        })
      )
    })
  })
}

const integration_test = (f) => {
  return new Promise((res, rej) => {
    const { props } = JSON.parse(fs.readFileSync(f))
    const store = createMockStore({ present: props })
    const component = shallowWithStore(<IProve />, store).dive()
    component.setState({ goalAchieved: [], "z3": [], "simple": false, "selectedTextBox": ["",-1] })
    component.instance().getRequiredSteps().then(() => {
      const steps = component.find(TextBoxList).at(2).dive().find(TextBox)
      expect(steps.length).toEqual(props.steps.length)
      steps.forEach((s) => {
        const cnames = s.dive().dive().props().className.split(" ")
        expect(cnames.indexOf('error') === -1).toEqual(true)
      })
      res()
    })
  })
}

const files = glob().readdirSync('**/*.proof')
files.forEach(f => {
  test('Integration test: ' + f, () => integration_test(f))
})