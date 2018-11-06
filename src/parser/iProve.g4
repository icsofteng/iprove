grammar iProve;

statement: expression;

parameter:
    VARIABLE                                                            # paramVar
  | CONSTANT                                                            # paramConst
  ;

expression:
    NOT expression                                                              # notExp
  | ASSUME expression                                                           # assumeExp
  | expression AND expression                                                   # andExp
  | expression OR expression                                                    # orExp
  | expression (IMPLIES|IMPLIES2|IMPLIES3) expression                           # impliesExp
  | expression (IFF|IFF2|IFF3) expression                                       # iffExp
  | LITERAL                                                                     # literalExp
  | TRUE                                                                        # trueExp
  | FALSE                                                                       # falseExp
  | EXIT                                                                        # exitExp
  | NAME BRACKET_OPEN (parameter (COMMA parameter)*)? BRACKET_CLOSE             # relationExp
  | BRACKET_OPEN expression BRACKET_CLOSE                                       # parenthesesExp
  | SQ_BRACKET_OPEN expression SQ_BRACKET_CLOSE                                 # sqParenthesesExp
  | FORALL VARIABLE expression                                                  # forallExp
  | EXISTS VARIABLE expression                                                  # existsExp
  | DEFINE NAME BRACKET_OPEN (TYPE (COMMA TYPE)*)? BRACKET_CLOSE COLON TYPE     # relationDefExp
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
LITERAL: [A-Z];
VARIABLE: [a-z];
CONSTANT: [A-Z][A-Za-z]+;
NAME: [a-z][a-zA-Z_]+;
TYPE: [A-Z][A-Za-z]+;
COMMA: ',';
COLON: ':';

WS: [ \t\r\n] -> skip;