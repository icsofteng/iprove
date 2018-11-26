import {parse} from '../'

const funcDef = {type:'funcDef', name:'friends', params:[{type: 'type', value: 'Person'}, {type: 'type', value: 'Person'}], returnType: {type:'type', value: 'Bool'}}
test("Visitor Test Func Def friends", ()=> {
    expect(parse("define friends(Person, Person):Bool")).toEqual({ast:[funcDef], identifiers: [], relations: [], functions: [{ name: 'friends', params:['Person', 'Person'], rType: 'Bool'}], types:['Person']})
  })


const funcDef2 = {type:'funcDef', name:'Power', params:[{type: 'type', value: 'Dragon'}, {type: 'type', value: 'Dragon'}], returnType: {type:'type', value: 'Int'}}
test("Visitor Test Func Def Dragon", ()=> {
    expect(parse("define Power(dragon, Dragon):int")).toEqual({ast:[funcDef2], identifiers: [], relations: [], functions: [{ name: 'Power', params:['Dragon', 'Dragon'], rType: 'Int'}], types:['Dragon']})
})

const funcDef3 = {type:'funcDef', name:'Happy', params:[{type: 'type', value: 'Dragon'}, {type: 'type', value: 'Human'}], returnType: {type:'type', value: 'Reward'}}
test("Visitor Test Func Def Happy", ()=> {
    expect(parse("define Happy(Dragon, Human):reward")).toEqual({ast:[funcDef3], identifiers: [], relations: [], functions: [{ name: 'Happy', params:['Dragon', 'Human'], rType: 'Reward'}], types:['Reward' ,'Dragon', 'Human']})
})

