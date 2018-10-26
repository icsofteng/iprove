grammar Propositional;

statement: expression;

expression:
    NOT expression                                                      # notExp
  | expression AND expression                                           # andExp
  | expression OR expression                                            # orExp
  | expression IMPLIES expression                                       # impliesExp
  | expression IFF expression                                           # iffExp
  | LITERAL                                                             # literalExp
  | TRUE                                                                # trueExp
  | FALSE                                                               # falseExp
  | BRACKET_OPEN expression BRACKET_CLOSE                               # parenthesesExp
  | FORALL VARIABLE BRACKET_OPEN expression BRACKET_CLOSE               # forallExp
  | EXISTS VARIABLE BRACKET_OPEN expression BRACKET_CLOSE               # existsExp
  | NAME BRACKET_OPEN parameter (COMMA parameter)* BRACKET_CLOSE        # relationExp
  ;

parameter:
    VARIABLE                                                            # paramVar
  | CONSTANT                                                            # paramConst
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
CONSTANT: [A-Z][a-z]+;
NAME: [a-z][a-zA-Z_]+;
COMMA: ',';

WS: [ \t\r\n] -> skip;