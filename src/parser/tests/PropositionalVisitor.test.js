import {parse} from '../'

test("Visitor Test implies", ()=> {
  expect(parse("P implies Q")).toMatchSnapshot()
})

test("Visitor Test and", ()=> {
  expect(parse("P and Q")).toMatchSnapshot()
})

test("Visitor Test iff", ()=> {
  expect(parse("P iff Q")).toMatchSnapshot()
})

test("Visitor Test or", ()=> {
  expect(parse("P or Q")).toMatchSnapshot()
})

test("Visitor Test not", ()=> {
  expect(parse("not P")).toMatchSnapshot()
})

test("Visitor Test literals", ()=> {
  expect(parse("P")).toMatchSnapshot()
  expect(parse("true")).toMatchSnapshot()
  expect(parse("false")).toMatchSnapshot()
})

test("Visitor Integrated Test", () => {
  expect(parse("(P and Q) implies (not X or Y)")).toMatchSnapshot()
})
