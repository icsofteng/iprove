## iProve
### Installing the app
1. Clone the repository `git clone git@github.com:icsofteng/iprove.git`
2. Run `npm install` to sync the dependencies.
3. Run `npm install -g nodemon` to install the node.js watcher

### Installing ANTLR
1. `cd /usr/local/lib`
2. `sudo curl -O http://www.antlr.org/download/antlr-4.7.1-complete.jar`
3. `export CLASSPATH=".:/usr/local/lib/antlr-4.7.1-complete.jar:$CLASSPATH"`
4. `alias antlr4='java -Xmx500M -cp "/usr/local/lib/antlr-4.7.1-complete.jar:$CLASSPATH" org.antlr.v4.Tool'`
5. `alias grun='java org.antlr.v4.gui.TestRig'`

### Running the app
1. In one terminal window, run `nodemon server.js`.
2. In another terminal, run `npm run build-dev`.
3. To run the tests, run `npm test`

### Building the parser
1. Rename `src/parser/iProveVisitor.js` temporarily to `visitor.js`
2. Run `antlr4 -Dlanguage=JavaScript -visitor src/parser/iProve.g4`
3. Delete `src/parser/iProveVisitor.js`
4. Rename `src/parser/visitor.js` to `iProveVisitor.js`

### Translation data structure
```
{ type: 'literal', value: true }                                                    (assert true)
{ type: 'literal', value: false }                                                   (assert false)
{ type: 'literal', value: 'P' }                                                     (assert P)
{ type: 'binary', symbol: 'implies', lhs: expr1, rhs: expr2 }                       (assert (=> expr1 expr2))
{ type: 'binary', symbol: 'iff', lhs: expr1, rhs: expr2 }                           (assert (iff expr1 expr2))
{ type: 'binary', symbol: 'and', lhs: expr1, rhs: expr2 }                           (assert (and expr1 expr2))
{ type: 'binary', symbol: 'or', lhs: expr1, rhs: expr2 }                            (assert (or expr1 expr2))
{ type: 'unary', symbol: 'not', value: expr }                                       (assert (not expr))
{ type: 'assume', value: expr }                                                     (assert (expr))

First Order:
{ type: 'quantifier', symbol: 'forall', variable: 'x', value: expr}                 (assert (forall ((x Type)) (expr)))
{ type: 'quantifier', symbol: 'exists', variable: 'x', value: expr}                 (assert (exists ((x Type)) (expr)))
{ type: 'variable', value: 'x'}                                                     x
{ type: 'relation', name: 'animal', params: [{variable|constant}]}                  (animal x y)
{ type: 'constant', value: 'Frank' }                                                Frank

Funcdef:
e.g.
define friends(Person, Person): Bool

{type:'funcDef', name:'friends', params:[{type: 'type', value: 'Person'}, {type: 'type', value: 'Person'}], returnType: {type:'type', value: 'Bool'}}
(declare-fun friends (Person Person) Bool)

let John, Bob: Person
friends(John, Bob)

Types for Quantifier:
forall x:Int (positive(x) <=> nonzero(x))
forall x:Int, y:human, z:money (Store(x,y) <=> make(z))



```

### Steps for translation
1. Print `declare-sort Type`
2. Loop through `relations` and foreach print `(declare-fun name (Type (, Type)*) Bool)`
3. Loop through `constants` and foreach print `(declare-const [symbol] Type)`
3. Loop through `literals` and foreach print `(declare-const [symbol] Bool)`
4. Loop through rules and print `(assert [rule])`
5. Negate final rule
6. End with (check-sat)
7. Response "unsat" if goal is true

### Server
http://iprove.eu-west-2.elasticbeanstalk.com
