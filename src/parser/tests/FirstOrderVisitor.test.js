import {parse} from '../'

const dragonX = { type: 'relation', name:"dragon", params:[{type:"variable", value:"x"}] }
const humanXYZ = { type: 'relation', name:"human", params:[{type:"variable", value:"x"}, {type:"variable", value:"y"}, {type:"variable", value:"z"}] }
const Frank = { type: 'relation', name:"person", params:[{type:"constant", value:"Frank"}]}

test("Visitor Test relations", ()=> {
  expect(parse("dragon(x)")).toEqual({ast:[dragonX], constants: [], atoms:[],relations: [{name: "dragon", numParam: 1}], types:[]})
})

test("Visitor Test forall", ()=> {
  expect(parse("forall x dragon(x)")).toEqual({ast:[{symbol:"forall", type: "universal_quantifier", value: dragonX, variables: [{type: "variable", value: "x", varType:'Type'}]}], constants: [], atoms:[], relations: [{name: "dragon", numParam: 1}], types:[]})
})

test("Visitor Test exists", ()=> {
  expect(parse("exists x dragon(x)")).toEqual({ast:[{symbol:"exists", type: "existential_quantifier", value: dragonX, variables: [{type: "variable", value: "x", varType:'Type'}]}], constants: [], atoms:[], relations: [{name: "dragon", numParam: 1}], types:[]})
})

test("Visitor Test params", ()=> {
  expect(parse("human(x, y, z)")).toEqual({ast:[humanXYZ], constants: [], atoms:[], relations: [{name: "human", numParam: 3}], types:[]})
})

test("Visitor Test relations", ()=> {
  expect(parse("person(Frank)")).toEqual({ast:[Frank], constants: ["Frank"], atoms:[], relations: [{name: "person", numParam: 1}], types:[]})
})

test("Visitor Test forall with type", ()=> {
  expect(parse("forall x:Int dragon(x)")).toEqual({ast:[{symbol:"forall", type: "universal_quantifier", value: dragonX, variables: [{type: "variable", value: "x", varType:'Type'}]}], constants: [], atoms:[], relations: [{name: "dragon", numParam: 1}], types:[]})
})

test("Visitor Test less than", () => {
  expect(parse("2 < 3")).toEqual({ ast: [{ lhs: { type: 'integer', value: 2 }, rhs: { type: 'integer', value: 3 }, symbol: 'less_than', type: 'binary_numerical' }], atoms: [], constants: [], relations: [], types: [] })
})

test("Visitor Test less than equal", () => {
  expect(parse("2 <= 3")).toEqual({ ast: [{ lhs: { type: 'integer', value: 2 }, rhs: { type: 'integer', value: 3 }, symbol: 'less_than_eq', type: 'binary_numerical' }], atoms: [], constants: [], relations: [], types: [] })
})

test("Visitor Test greater than", () => {
  expect(parse("2 > 3")).toEqual({ ast: [{ lhs: { type: 'integer', value: 2 }, rhs: { type: 'integer', value: 3 }, symbol: 'greater_than', type: 'binary_numerical' }], atoms: [], constants: [], relations: [], types: [] })
})

test("Visitor Test greater than equal", () => {
  expect(parse("2 >= 3")).toEqual({ ast: [{ lhs: { type: 'integer', value: 2 }, rhs: { type: 'integer', value: 3 }, symbol: 'greater_than_eq', type: 'binary_numerical' }], atoms: [], constants: [], relations: [], types: [] })
})

test("Visitor Test equal", () => {
  expect(parse("2 == 3")).toEqual({ ast: [{ lhs: { type: 'integer', value: 2 }, rhs: { type: 'integer', value: 3 }, symbol: 'equal', type: 'binary_numerical' }], atoms: [], constants: [], relations: [], types: [] })
})

test("Visitor Test plus", () => {
  expect(parse("2 + 3")).toEqual({ ast: [{ lhs: { type: 'integer', value: 2 }, rhs: { type: 'integer', value: 3 }, symbol: 'plus', type: 'binary_numerical' }], atoms: [], constants: [], relations: [], types: [] })
})

test("Visitor Test minus", () => {
  expect(parse("2 - 3")).toEqual({ ast: [{ lhs: { type: 'integer', value: 2 }, rhs: { type: 'integer', value: 3 }, symbol: 'minus', type: 'binary_numerical' }], atoms: [], constants: [], relations: [], types: [] })
})

test("Visitor Test power", () => {
  expect(parse("2 ^ 3")).toEqual({ ast: [{ lhs: { type: 'integer', value: 2 }, rhs: { type: 'integer', value: 3 }, symbol: 'power', type: 'binary_numerical' }], atoms: [], constants: [], relations: [], types: [] })
})

test("Visitor Test multiply", () => {
  expect(parse("2 * 3")).toEqual({ ast: [{ lhs: { type: 'integer', value: 2 }, rhs: { type: 'integer', value: 3 }, symbol: 'multiply', type: 'binary_numerical' }], atoms: [], constants: [], relations: [], types: [] })
})

test("Visitor Test divide", () => {
  expect(parse("2 / 3")).toEqual({ ast: [{ lhs: { type: 'integer', value: 2 }, rhs: { type: 'integer', value: 3 }, symbol: 'divide', type: 'binary_numerical' }], atoms: [], constants: [], relations: [], types: [] })
})
