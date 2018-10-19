## iProve
### Installation
1. Clone the repository `git clone git@github.com:icsofteng/iprove.git`
2. Run `npm install` to sync the dependencies.
3. Run `npm install -g nodemon` to install the node.js watcher

### Running
1. In one terminal window, run `nodemon server.js`.
2. In another terminal, run `npm run build-dev`.
3. To run the tests, run `npm test`

### Translation data structure
```
{ type: 'literal', value: true }                                   (assert true)
{ type: 'literal', value: false }                                  (assert false)
{ type: 'literal', value: 'p' }                                    (assert p)
{ type: 'binary', symbol: 'implies', lhs: expr1, rhs: expr2 }      (assert (=> expr1 expr2))
{ type: 'binary', symbol: 'iff', lhs: expr1, rhs: expr2 }          (assert (iff expr1 expr2))
{ type: 'binary', symbol: 'and', lhs: expr1, rhs: expr2 }          (assert and expr1 expr2)
{ type: 'binary', symbol: 'or', lhs: expr1, rhs: expr2 }           (assert or expr1 expr2)
{ type: 'unary', symbol: 'not', value: expr }                      (assert not expr)
```

### Steps for translation
1. Loop through `constants` and foreach print `(declare-const [symbol] Bool)`
2. Loop through rules and print `(assert [rule])`
3. Negate final rule
4. End with (check-sat)
5. Response "unsat" if goal is true

LIVE LINK : http://iprove.eu-west-2.elasticbeanstalk.com
