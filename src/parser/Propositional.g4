grammar Propositional;

expression:
  BRACKET_OPEN expression BRACKET_CLOSE |
  NOT expression |
  expression AND expression |
  expression OR expression |
  expression IMPLIES expression |
  expression IFF expression |
  LITERAL |
  TRUE |
  FALSE;

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