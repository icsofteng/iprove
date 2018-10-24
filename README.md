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
1. Rename `src/parser/PropositionalVisitor.js` temporarily to `visitor.js`
2. Run `antlr4 -Dlanguage=JavaScript -visitor src/parser/Propositional.g4`
3. Delete `src/parser/PropositionalVisitor.js`
4. Rename `src/parser/visitor.js` to `PropositionalVisitor.js`

### Translation data structure
```
{ type: 'literal', value: true }                                                    (assert true)
{ type: 'literal', value: false }                                                   (assert false)
{ type: 'literal', value: 'p' }                                                     (assert p)
{ type: 'binary', symbol: 'implies', lhs: expr1, rhs: expr2 }                       (assert (=> expr1 expr2))
{ type: 'binary', symbol: 'iff', lhs: expr1, rhs: expr2 }                           (assert (iff expr1 expr2))
{ type: 'binary', symbol: 'and', lhs: expr1, rhs: expr2 }                           (assert (and expr1 expr2))
{ type: 'binary', symbol: 'or', lhs: expr1, rhs: expr2 }                            (assert (or expr1 expr2))
{ type: 'unary', symbol: 'not', value: expr }                                       (assert (not expr))

First Order:
{ type: 'quantifier', symbol: 'forall', variable: var, value: expr} 
                                                                (assert (forall ((var Type)) (expr)))
{ type: 'quantifier', symbol: 'exists', variable: var, value: expr} 
                                                                (assert (exists ((var Type)) (expr)))
{ type: 'variable', var: var, varType:{'Real/Bool/Int'}}


{ type: 'varType', value: 'Real' }
{ type: 'varType', value: 'Bool' }
{ type: 'varType', value: 'Int' }
{ type: 'varType', value: 'Type } // used to define a sort 'Type' for generic constants e.g. 'Frank' in logic
// TODO: user defined types

{ type: 'relation', name: '...', vars: [{variable}]}                                 (name var (, var))
                                                                                     (declare-fun name (Type (, Type)*) Bool)

{ type: 'function', name: '...', vars: [{variable}]}                                 (name var (, var))
{ type: 'functionDef', name: '...' inputTypes: [varTypes], outputType: varType }     (declare-fun name (varType (, varType)*), varType)


{ type: 'constant', name: '...' }                                               (declare-sort name varType)
```

### Steps for translation
1. Loop through `literals` and foreach print `(declare-const [symbol] Bool)`
2. Loop through rules and print `(assert [rule])`
3. Negate final rule
4. End with (check-sat)
5. Response "unsat" if goal is true

### Server
http://iprove.eu-west-2.elasticbeanstalk.com
