import {parse} from '../'

const dragonX = { type: 'relation', name:"dragon", params:[{type:"identifier", value:"x", varType: "Bool"}] }
const dragonInt = { type: 'relation', name:"dragon", params:[{type:"identifier", value:"x", varType: "Int"}] }
const humanXYZ = { type: 'relation', name:"human", params:[{type:"identifier", value:"x", varType: "Bool"}, {type:"identifier", value:"y", varType: "Bool"}, {type:"identifier", value:"z", varType: "Bool"}] }
const Frank = { type: 'relation', name:"person", params:[{type:"identifier", value:"Frank", varType: "Bool"}]}

test("Visitor Test relations 1", ()=> {
  expect(parse("dragon(x)")).toEqual({ast:[dragonX], identifiers: [{ value: "x", varType: "Bool"}], relations: [{name: "dragon", numParam: 1, params: [{ type: "identifier", value: "x", varType: "Bool"}]}], types:[]})
})

test("Visitor Test forall", ()=> {
  expect(parse("forall x dragon(x)")).toEqual({ast:[{symbol:"forall", type: "universal_quantifier", value: dragonX, variables: [{type: "identifier", value: "x", varType: "Bool"}]}], identifiers: [],  relations: [{name: "dragon", numParam: 1, params: [{ type: "identifier", value: "x", varType: "Bool"}]}], types:[]})
})

test("Visitor Test exists", ()=> {
  expect(parse("exists x dragon(x)")).toEqual({ast:[{symbol:"exists", type: "existential_quantifier", value: dragonX, variables: [{type: "identifier", value: "x", varType: "Bool"}]}], identifiers: [],  relations: [{name: "dragon", numParam: 1, params: [{ type: "identifier", value: "x", varType: "Bool"}]}], types:[]})
})

test("Visitor Test params", ()=> {
  expect(parse("human(x, y, z)")).toEqual({ast:[humanXYZ], identifiers: [{value:"x", varType: "Bool"}, {value:"y", varType: "Bool"}, {value:"z", varType: "Bool"}],  relations: [{name: "human", numParam: 3, params: [{ type: "identifier", value: "x", varType: "Bool"}, { type: "identifier", value: "y", varType: "Bool"}, { type: "identifier", value: "z", varType: "Bool"}]}], types:[]})
})

test("Visitor Test relations for person", ()=> {
  expect(parse("person(Frank)")).toEqual({ast:[Frank], identifiers: [{ value:"Frank", varType: "Bool"}],  relations: [{name: "person", numParam: 1, params: [{"type": "identifier", "value": "Frank","varType": "Bool"}]}], types:[]})
})

test("Visitor Test forall with type", ()=> {
  expect(parse("forall x:Int dragon(x)")).toEqual({ast:[{symbol:"forall", type: "universal_quantifier", value: dragonInt, variables: [{type: "identifier", value: "x", varType:'Int'}]}], identifiers: [],  relations: [{name: "dragon", numParam: 1, params: [{ type: "identifier", value: "x", varType: "Int"}]}], types:[]})
})

test("Visitor Test less than", () => {
  expect(parse("2 < 3")).toEqual({ ast: [{ lhs: { type: 'integer', value: 2 }, rhs: { type: 'integer', value: 3 }, symbol: 'less_than', type: 'binary_numerical' }],  identifiers: [], relations: [], types: [] })
})

test("Visitor Test less than equal", () => {
  expect(parse("2 <= 3")).toEqual({ ast: [{ lhs: { type: 'integer', value: 2 }, rhs: { type: 'integer', value: 3 }, symbol: 'less_than_eq', type: 'binary_numerical' }],  identifiers: [], relations: [], types: [] })
})

test("Visitor Test greater than", () => {
  expect(parse("2 > 3")).toEqual({ ast: [{ lhs: { type: 'integer', value: 2 }, rhs: { type: 'integer', value: 3 }, symbol: 'greater_than', type: 'binary_numerical' }],  identifiers: [], relations: [], types: [] })
})

test("Visitor Test greater than equal", () => {
  expect(parse("2 >= 3")).toEqual({ ast: [{ lhs: { type: 'integer', value: 2 }, rhs: { type: 'integer', value: 3 }, symbol: 'greater_than_eq', type: 'binary_numerical' }],  identifiers: [], relations: [], types: [] })
})

test("Visitor Test equal", () => {
  expect(parse("2 == 3")).toEqual({ ast: [{ lhs: { type: 'integer', value: 2 }, rhs: { type: 'integer', value: 3 }, symbol: 'equal', type: 'binary_numerical' }],  identifiers: [], relations: [], types: [] })
})

test("Visitor Test plus", () => {
  expect(parse("2 + 3")).toEqual({ ast: [{ lhs: { type: 'integer', value: 2 }, rhs: { type: 'integer', value: 3 }, symbol: 'plus', type: 'binary_numerical' }],  identifiers: [], relations: [], types: [] })
})

test("Visitor Test minus", () => {
  expect(parse("2 - 3")).toEqual({ ast: [{ lhs: { type: 'integer', value: 2 }, rhs: { type: 'integer', value: 3 }, symbol: 'minus', type: 'binary_numerical' }],  identifiers: [], relations: [], types: [] })
})

test("Visitor Test power", () => {
  expect(parse("2 ^ 3")).toEqual({ ast: [{ lhs: { type: 'integer', value: 2 }, rhs: { type: 'integer', value: 3 }, symbol: 'power', type: 'binary_numerical' }],  identifiers: [], relations: [], types: [] })
})

test("Visitor Test multiply", () => {
  expect(parse("2 * 3")).toEqual({ ast: [{ lhs: { type: 'integer', value: 2 }, rhs: { type: 'integer', value: 3 }, symbol: 'multiply', type: 'binary_numerical' }],  identifiers: [], relations: [], types: [] })
})

test("Visitor Test divide", () => {
  expect(parse("2 / 3")).toEqual({ ast: [{ lhs: { type: 'integer', value: 2 }, rhs: { type: 'integer', value: 3 }, symbol: 'divide', type: 'binary_numerical' }],  identifiers: [], relations: [], types: [] })
})
