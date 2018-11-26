import {parse} from '../'

const p = {type:'identifier', value:"P", varType: "Bool" }
const q = {type:'identifier', value:"Q", varType: "Bool" }

test("Visitor Test implies", ()=> {
  expect(parse("P implies Q")).toEqual({ast:[{type:'binary', symbol:'implies', lhs: p, rhs:q}], identifiers: [{ value: "P", varType: "Bool"}, {value: "Q", varType: "Bool"}], "relations":[], functions: [], types:[]})
})

test("Visitor Test and", ()=> {
  expect(parse("P and Q")).toEqual({ast:[{type:'binary', symbol:'and', lhs:p, rhs:q}], identifiers: [{ value: "P", varType: "Bool"}, {value: "Q", varType: "Bool"}], "relations":[], functions: [], types:[]})
})

test("Visitor Test iff", ()=> {
  expect(parse("P iff Q")).toEqual({ast:[{type:'binary', symbol:'iff', lhs:p, rhs:q}], identifiers: [{ value: "P", varType: "Bool"}, {value: "Q", varType: "Bool"}], "relations":[], functions: [], types:[]})
})

test("Visitor Test or", ()=> {
  expect(parse("P or Q")).toEqual({ast:[{type:'binary', symbol:'or', lhs:p, rhs:q}], identifiers: [{ value: "P", varType: "Bool"}, {value: "Q", varType: "Bool"}], "relations":[], functions: [], types:[]})
})

test("Visitor Test not", ()=> {
  expect(parse("not P")).toEqual({ast:[{type:'unary', symbol:'not', value:p}], identifiers: [{ value: "P", varType: "Bool"}], "relations":[], functions: [], types:[]})
})

test("Visitor Test literals", ()=> {
  expect(parse("P")).toEqual({ast:[p], identifiers: [{ value: "P", varType: "Bool"}], "relations":[], functions: [], types:[]})
  expect(parse("true")).toEqual( {ast:[{type:'true'}], identifiers: [], "relations":[], functions: [], types:[]})
  expect(parse("false")).toEqual( {ast:[{type:'false'}], identifiers: [], "relations":[], functions: [], types:[]})
})

test("Visitor Integrated Test", () => {
  const x = {type:'identifier', value:"X", varType: "Bool" }
  const y = {type:'identifier', value:"Y", varType: "Bool" }
  const lhs2 = {type:'binary', symbol:'and', lhs:p, rhs:q}
  const rhs2 = {type:'binary', symbol:'or', lhs:{type:"unary", symbol:"not", value:x }, rhs:y}
  const bracketL = {type:"paren", value:lhs2}
  const bracketR = {type:"paren", value:rhs2}

  expect(parse("(P and Q) implies (not X or Y)")).toEqual(
    {ast:[{type:'binary', symbol:'implies', lhs:bracketL , rhs:bracketR}], identifiers: [{ value: "P", varType: "Bool"}, {value: "Q", varType: "Bool"}, {value: "X", varType: "Bool"}, {value: "Y", varType: "Bool"}], "relations":[], functions: [], types:[]}
  )
})
