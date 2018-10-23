import {parse} from './'
import { notDeepEqual } from 'assert';

const p = {type: 'literal', value: "p" }
const q = {type: 'literal', value: "q" }

let value
test("Visitor Test implies", ()=> {
  expect(parse("p implies q")).toEqual([{type: 'binary', symbol: 'implies', lhs: p, rhs:q}])
})

test("Visitor Test and", ()=> {
  expect(parse("p and q")).toEqual([{type: 'binary', symbol: 'and', lhs: p, rhs:q}])
})

test("Visitor Test iff", ()=> {
  expect(parse("p iff q")).toEqual([{type: 'binary', symbol: 'iff', lhs: p, rhs:q}])
})

test("Visitor Test or", ()=> {
  expect(parse("p or q")).toEqual([{type: 'binary', symbol: 'or', lhs: p, rhs:q}])
})

test("Visitor Test not", ()=> {
  expect(parse("not p")).toEqual([{type: 'unary', symbol: 'not', value: p}])
})

test("Visitor Test literals", ()=> {
  expect(parse("p")).toEqual([p])
  expect(parse("true")).toEqual([{type: 'true'}])
  expect(parse("false")).toEqual([{type: 'false'}])
})

test("Visitor Integrated Test", () => {
  let x = {type: 'literal', value: "x" }
  let y = {type: 'literal', value: "y" }
  value = x
  let lhs2 = {type: 'binary', symbol: 'and', lhs:p, rhs:q}
  let rhs2 = {type: 'binary', symbol: 'or', lhs:{type: "unary", symbol: "not", value: x },rhs: y}
  expect(parse("(p and q) implies (not x or y)")).toEqual(
    [{type: 'binary', symbol: 'implies', lhs:lhs2 , rhs:rhs2}]
    )
})
