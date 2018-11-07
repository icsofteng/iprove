import {parse} from '../'

const funcDef = {type:'funcDef', name:'friends', params:[{type: 'type', value: 'Person'}, {type: 'type', value: 'Person'}], returnType: {type:'type', value: 'Bool'}}
test("Visitor Test relations", ()=> {
    expect(parse("define friends(Person, Person):Bool")).toEqual({ast:[funcDef], constants: [], atoms:[],relations: [{name: "friends", numParam: 2}]})
  })
