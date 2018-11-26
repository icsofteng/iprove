import {parse} from '../'

test("Visitor Test Func Def friends", ()=> {
    expect(parse("define friends(Person, Person):Bool")).toMatchSnapshot()
  })

test("Visitor Test Func Def Dragon", ()=> {
    expect(parse("define Power(dragon, Dragon):int")).toMatchSnapshot()
})

test("Visitor Test Func Def Happy", ()=> {
    expect(parse("define Happy(Dragon, Human):reward")).toMatchSnapshot()
})

