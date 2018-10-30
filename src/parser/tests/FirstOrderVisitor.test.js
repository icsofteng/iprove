import {parse} from '../'

const dragonX = { type: 'relation', name:"dragon", params:[{type:"variable", value:"x"}] }
const humanXYZ = { type: 'relation', name:"human", params:[{type:"variable", value:"x"}, {type:"variable", value:"y"}, {type:"variable", value:"z"}] }
const Frank = { type: 'relation', name:"person", params:[{type:"constant", value:"Frank"}]}

test("Visitor Test relations", ()=> {
  expect(parse("dragon(x)")).toEqual({ast:[dragonX], constants: [], atoms:[],relations: [{name: "dragon", numParam: 1}]})
})

test("Visitor Test forall", ()=> {
  expect(parse("forall x dragon(x)")).toEqual({ast:[{symbol:"forall", type: "quantifier", value: dragonX, variable: "x"}], constants: [], atoms:[], relations: [{name: "dragon", numParam: 1}]})
})

test("Visitor Test exists", ()=> {
  expect(parse("exists x dragon(x)")).toEqual({ast:[{symbol:"exists", type: "quantifier", value: dragonX, variable: "x"}], constants: [], atoms:[], relations: [{name: "dragon", numParam: 1}]})
})

test("Visitor Test params", ()=> {
  expect(parse("human(x, y, z)")).toEqual({ast:[humanXYZ], constants: [], atoms:[], relations: [{name: "human", numParam: 3}]})
})

test("Visitor Test ", ()=> {
  expect(parse("person(Frank)")).toEqual({ast:[Frank], constants: ["Frank"], atoms:[], relations: [{name: "person", numParam: 1}]})
})
