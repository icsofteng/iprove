import {parse} from '../'

test("Visitor Test relations", ()=> {
    expect(parse("define friends(Person, Person):Bool")).toEqual({type:'funcDef', name:'friends', params:[{type: 'type', value: 'Person'}, {type: 'type', value: 'Person'}]})
  })