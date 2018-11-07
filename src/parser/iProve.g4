grammar iProve;

statement: expression;

parameter:
    VARIABLE                                                            # paramVar
  | IDENTIFIER                                                          # paramConst
  ;

expression:
  NOT expression                                                                                      # notExp
| ASSUME expression                                                                                   # assumeExp
| expression AND expression                                                                           # andExp
| expression OR expression                                                                            # orExp
| expression (IMPLIES|IMPLIES2|IMPLIES3) expression                                                   # impliesExp
| expression (IFF|IFF2|IFF3) expression                                                               # iffExp
| TRUE                                                                                                # trueExp
| FALSE                                                                                               # falseExp
| EXIT                                                                                                # exitExp
| DEFINE IDENTIFIER BRACKET_OPEN (parameter (COMMA parameter)*)? BRACKET_CLOSE COLON IDENTIFIER       # relationDefExp
| IDENTIFIER BRACKET_OPEN (parameter (COMMA parameter)*)? BRACKET_CLOSE                               # relationExp
| BRACKET_OPEN expression BRACKET_CLOSE                                                               # parenthesesExp
| SQ_BRACKET_OPEN expression SQ_BRACKET_CLOSE                                                         # sqParenthesesExp
| FORALL VARIABLE expression                                                                          # forallExp
| EXISTS VARIABLE expression                                                                          # existsExp
| IDENTIFIER                                                                                          # literalExp
;

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
IDENTIFIER: [A-Za-z]+;
COMMA: ',';
COLON: ':';

WS: [ \t\r\n] -> skip;