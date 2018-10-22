grammar Propositional;

statement: expression;

expression:
    NOT expression                            # notExp
  | expression AND expression                 # andExp
  | expression OR expression                  # orExp
  | expression IMPLIES expression             # impliesExp
  | expression IFF expression                 # iffExp
  | LITERAL                                   # literalExp
  | TRUE                                      # trueExp
  | FALSE                                     # falseExp
  | BRACKET_OPEN expression BRACKET_CLOSE     # parenthesesExp
  ;

LITERAL: [a-z];
NOT: 'not';
AND: 'and';
OR: 'or';
IMPLIES: 'implies';
IFF: 'iff';
TRUE: 'true';
FALSE: 'false';
BRACKET_OPEN: '(';
BRACKET_CLOSE: ')';

WS: [ \t\r\n] -> skip;