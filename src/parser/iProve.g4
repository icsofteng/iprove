grammar iProve;

statement: expression;

parameter:
    VARIABLE                                                            # paramVar
  | IDENTIFIER                                                          # paramIdent
  ;

variableDef: VARIABLE (COLON IDENTIFIER)?;

expression:
  NOT expression                                                                                      # notExp
| BRACKET_OPEN expression BRACKET_CLOSE                                                               # parenthesesExp
| SQ_BRACKET_OPEN expression SQ_BRACKET_CLOSE                                                         # sqParenthesesExp
| ASSUME expression                                                                                   # assumeExp
| expression POWER expression                                                                         # powerExp
| expression DIVIDE expression                                                                        # divideExp
| expression MULTIPLY expression                                                                      # multiplyExp
| expression PLUS expression                                                                          # plusExp
| expression MINUS expression                                                                         # minusExp
| expression DOUBLEEQUALS expression                                                                  # equalExp
| expression LESSTHAN expression                                                                      # lessThanExp
| expression LESSTHANEQ expression                                                                    # lessThanEqExp
| expression GREATERTHAN expression                                                                   # greaterThanExp
| expression GREATERTHANEQ expression                                                                 # greaterThanEqExp
| expression AND expression                                                                           # andExp
| expression OR expression                                                                            # orExp
| expression (IMPLIES|IMPLIES2|IMPLIES3) expression                                                   # impliesExp
| expression (IFF|IFF2|IFF3) expression                                                               # iffExp
| CASE                                                                                                # caseExp
| TRUE                                                                                                # trueExp
| FALSE                                                                                               # falseExp
| EXIT                                                                                                # exitExp
| INTEGER                                                                                             # integerExp
| REAL                                                                                                # realExp
| ATOM                                                                                                # atomExp
| DEFINE IDENTIFIER BRACKET_OPEN (parameter (COMMA parameter)*)? BRACKET_CLOSE COLON IDENTIFIER       # relationDefExp
| IDENTIFIER BRACKET_OPEN (parameter (COMMA parameter)*)? BRACKET_CLOSE                               # relationExp
| FORALL variableDef POINT? (COMMA variableDef)* expression                                           # forallExp
| EXISTS variableDef POINT? (COMMA variableDef)* expression                                           # existsExp
| IDENTIFIER (COLON IDENTIFIER)?                                                                      # identifierExp
| VARIABLE                                                                                            # variableExp
;

CASE: 'case';
ASSUME: 'assume';
FORALL: 'forall';
DEFINE: 'define';
EXISTS: 'exists';
EXIT: 'exit';
NOT: 'not';
AND: 'and';
OR: 'or';
IMPLIES: 'implies';
IMPLIES2: '=>';
IMPLIES3: '->';
IFF: 'iff';
IFF2: '<=>';
IFF3: '<->';
TRUE: 'true';
FALSE: 'false';
BRACKET_OPEN: '(';
BRACKET_CLOSE: ')';
SQ_BRACKET_OPEN: '[';
SQ_BRACKET_CLOSE: ']';
VARIABLE: [a-z];
ATOM: [A-Z];
IDENTIFIER: [A-Za-z]+;
COMMA: ',';
COLON: ':';
INTEGER: [0-9]+;
REAL: [0-9]*[.][0-9]+;
LESSTHAN: '<';
LESSTHANEQ: '<=';
GREATERTHAN: '>';
GREATERTHANEQ: '>=';
DOUBLEEQUALS: '==';
PLUS: '+';
MINUS: '-';
POWER: '^';
MULTIPLY: '*';
DIVIDE: '/';
POINT: '.';

WS: [ \t\r\n] -> skip;
