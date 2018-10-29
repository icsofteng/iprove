grammar Propositional;

statement: expression;

  parameter:
    VARIABLE                                                            # paramVar
  | CONSTANT                                                            # paramConst
  ;

expression:
    NOT expression                                                      # notExp
  | expression AND expression                                           # andExp
  | expression OR expression                                            # orExp
  | expression IMPLIES expression                                       # impliesExp
  | expression IFF expression                                           # iffExp
  | LITERAL                                                             # literalExp
  | TRUE                                                                # trueExp
  | FALSE                                                               # falseExp
  | NAME BRACKET_OPEN (parameter (COMMA parameter)*)? BRACKET_CLOSE     # relationExp
  | BRACKET_OPEN expression BRACKET_CLOSE                               # parenthesesExp
  | FORALL VARIABLE expression                                          # forallExp
  | EXISTS VARIABLE expression                                          # existsExp
  ;

FORALL: 'forall';
EXISTS: 'exists';
NOT: 'not';
AND: 'and';
OR: 'or';
IMPLIES: 'implies';
IFF: 'iff';
TRUE: 'true';
FALSE: 'false';
BRACKET_OPEN: '(';
BRACKET_CLOSE: ')';
LITERAL: [A-Z];
VARIABLE: [a-z];
CONSTANT: [A-Z][A-Za-z]+;
NAME: [a-z][a-zA-Z_]+;
COMMA: ',';

WS: [ \t\r\n] -> skip;