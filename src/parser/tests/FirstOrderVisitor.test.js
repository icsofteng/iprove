import {parse} from '../'

test("Visitor Test relations 1", ()=> {
  expect(parse("dragon(x)")).toMatchSnapshot()
})

test("Visitor Test forall", ()=> {
  expect(parse("forall x dragon(x)")).toMatchSnapshot()
})

test("Visitor Test exists", ()=> {
  expect(parse("exists x dragon(x)")).toMatchSnapshot()
})

test("Visitor Test params", ()=> {
  expect(parse("human(x, y, z)")).toMatchSnapshot()
})

test("Visitor Test relations for person", ()=> {
  expect(parse("person(Frank)")).toMatchSnapshot()
})

test("Visitor Test forall with type", ()=> {
  expect(parse("forall x:Int dragon(x)")).toMatchSnapshot()
})

test("Visitor Test less than", () => {
  expect(parse("2 < 3")).toMatchSnapshot()
})

test("Visitor Test less than equal", () => {
  expect(parse("2 <= 3")).toMatchSnapshot()
})

test("Visitor Test greater than", () => {
  expect(parse("2 > 3")).toMatchSnapshot()
})

test("Visitor Test greater than equal", () => {
  expect(parse("2 >= 3")).toMatchSnapshot()
})

test("Visitor Test equal", () => {
  expect(parse("2 == 3")).toMatchSnapshot()
})

test("Visitor Test plus", () => {
  expect(parse("2 + 3")).toMatchSnapshot()
})

test("Visitor Test minus", () => {
  expect(parse("2 - 3")).toMatchSnapshot()
})

test("Visitor Test power", () => {
  expect(parse("2 ^ 3")).toMatchSnapshot()
})

test("Visitor Test multiply", () => {
  expect(parse("2 * 3")).toMatchSnapshot()
})

test("Visitor Test divide", () => {
  expect(parse("2 / 3")).toMatchSnapshot()
})
