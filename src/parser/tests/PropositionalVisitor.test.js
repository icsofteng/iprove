import {parse} from '../'

const p = {type:'literal', value:"P" }
const q = {type:'literal', value:"Q" }

test("Visitor Test implies", ()=> {
  expect(parse("P implies Q")).toEqual({ast:[{type:'binary', symbol:'implies', lhs: p, rhs:q}], constants: [], atoms:["P", "Q"], "relations":[], types:[]})
})

test("Visitor Test and", ()=> {
  expect(parse("P and Q")).toEqual({ast:[{type:'binary', symbol:'and', lhs:p, rhs:q}], constants: [], atoms:["P", "Q"], "relations":[], types:[]})
})

test("Visitor Test iff", ()=> {
  expect(parse("P iff Q")).toEqual({ast:[{type:'binary', symbol:'iff', lhs:p, rhs:q}], constants: [], atoms:["P", "Q"], "relations":[], types:[]})
})

test("Visitor Test or", ()=> {
  expect(parse("P or Q")).toEqual({ast:[{type:'binary', symbol:'or', lhs:p, rhs:q}], constants: [], atoms:["P", "Q"], "relations":[], types:[]})
})

test("Visitor Test not", ()=> {
  expect(parse("not P")).toEqual({ast:[{type:'unary', symbol:'not', value:p}], constants: [], atoms:["P"], "relations":[], types:[]})
})

test("Visitor Test literals", ()=> {
  expect(parse("P")).toEqual({ast:[p], constants: [], atoms:["P"], "relations":[], types:[]})
  expect(parse("true")).toEqual( {ast:[{type:'true'}], constants: [], atoms:[], "relations":[], types:[]})
  expect(parse("false")).toEqual( {ast:[{type:'false'}], constants: [], atoms:[], "relations":[], types:[]})
})

test("Visitor Integrated Test", () => {
  const x = {type:'literal', value:"X" }
  const y = {type:'literal', value:"Y" }
  const lhs2 = {type:'binary', symbol:'and', lhs:p, rhs:q}
  const rhs2 = {type:'binary', symbol:'or', lhs:{type:"unary", symbol:"not", value:x }, rhs:y}
  const bracketL = {type:"paren", value:lhs2}
  const bracketR = {type:"paren", value:rhs2}

  expect(parse("(P and Q) implies (not X or Y)")).toEqual(
    {ast:[{type:'binary', symbol:'implies', lhs:bracketL , rhs:bracketR}], constants: [], atoms:["P", "Q", "X", "Y"], "relations":[], types:[]}
  )
})
