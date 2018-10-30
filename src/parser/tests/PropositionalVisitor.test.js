import {parse} from '../'

const p = {type:'literal', value:"P" }
const q = {type:'literal', value:"Q" }

test("Visitor Test implies", ()=> {
  expect(parse("P implies Q")).toEqual({ast:[{type:'binary', symbol:'implies', lhs: p, rhs:q}], constants:["P", "Q"], "relations":[]})
})

test("Visitor Test and", ()=> {
  expect(parse("P and Q")).toEqual({ast:[{type:'binary', symbol:'and', lhs:p, rhs:q}], constants:["P", "Q"], "relations":[]})
})

test("Visitor Test iff", ()=> {
  expect(parse("P iff Q")).toEqual({ast:[{type:'binary', symbol:'iff', lhs:p, rhs:q}], constants:["P", "Q"], "relations":[]})
})

test("Visitor Test or", ()=> {
  expect(parse("P or Q")).toEqual({ast:[{type:'binary', symbol:'or', lhs:p, rhs:q}], constants:["P", "Q"], "relations":[]})
})

test("Visitor Test not", ()=> {
  expect(parse("not P")).toEqual({ast:[{type:'unary', symbol:'not', value:p}], constants:["P"], "relations":[]})
})

test("Visitor Test literals", ()=> {
  expect(parse("P")).toEqual({ast:[p], constants:["P"], "relations":[]})
  expect(parse("true")).toEqual( {ast:[{type:'true'}], constants:[], "relations":[]})
  expect(parse("false")).toEqual( {ast:[{type:'false'}], constants:[], "relations":[]})
})

test("Visitor Integrated Test", () => {
  const x = {type:'literal', value:"X" }
  const y = {type:'literal', value:"Y" }
  const lhs2 = {type:'binary', symbol:'and', lhs:p, rhs:q}
  const rhs2 = {type:'binary', symbol:'or', lhs:{type:"unary", symbol:"not", value:x }, rhs:y}
  const bracketL = {type:"paren", value:lhs2}
  const bracketR = {type:"paren", value:rhs2}

  expect(parse("(P and Q) implies (not X or Y)")).toEqual(
    {ast:[{type:'binary', symbol:'implies', lhs:bracketL , rhs:bracketR}], constants:["P", "Q", "X", "Y"], "relations":[]}
  )
})
