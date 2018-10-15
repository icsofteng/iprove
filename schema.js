var constants = ['p', 'q']

var rules = [
  {
    type: 'implies',
    lhs: {
      type: 'literal',
      value : 'p'
    },
    rhs: 'q'
  },
  {
    type: 'literal',
    value: 'p'
  }
]

// Translation
// { type: 'literal', value: true }                 (assert true)
// { type: 'literal', value: false }                (assert false)
// { type: 'literal', value: 'p' }                  (assert p)
// { type: 'implies', lhs: expr1, rhs: expr2 }      (assert (=> expr1 expr2))
// { type: 'iff', lhs: expr1, rhs: expr2 }          (assert (iff expr1 expr2))
// { type: 'and', lhs: expr1, rhs: expr2 }          (assert and expr1 expr2)
// { type: 'or', lhs: expr1, rhs: expr2 }           (assert or expr1 expr2)
// { type: 'not', value: expr }                     (assert not expr)



// Steps:
// 1. Loop through `constants` and foreach print (declare-const [symbol] Bool)
// 2. Loop through rules and print (assert [rule])
// 3. Negate final rule
// 4. End with (check-sat)
// 5. Response "unsat" if goal is true