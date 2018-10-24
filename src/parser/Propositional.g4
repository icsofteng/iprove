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
  | FORALL variable BRACKET_OPEN expression BRACKET_CLOSE               # forallExp
  | EXISTS variable BRACKET_OPEN expression BRACKET_CLOSE               # existsExp
  | NAME BRACKET_OPEN variable (COMMA variable)* BRACKET_CLOSE          # function
  | DEFINE NAME BRACKET_OPEN varType (Comma varType)* BRACKET_CLOSE     # functionDef
  ;



variable:
  | VARIABLE                                   # literalVar
  | VARIABLE COLON varType                     # literalTypeVar
  ;

varType:
  | TYPE_BOOL                                 # varTypeBool
  | TYPE_INT                                  # varTypeInt
  | TYPE_REAL                                 # varTypeReal
  ;

/* Propositional logic */
LITERAL: [A-Z];
NOT: 'not';
AND: 'and';
OR: 'or';
IMPLIES: 'implies';
IFF: 'iff';
TRUE: 'true';
FALSE: 'false';
BRACKET_OPEN: '(';
BRACKET_CLOSE: ')';

/* Predicate logic only */
VARIABLE: [a-z]
CONSTANT: LITERAL CHARACTER*
NAME: LETTER CHARACTER*
fragment CHARACTER: (LETTER | DIGIT | '_' | '`');
fragment LETTER: ('a'..'z' | 'A'..'Z');
fragment DIGIT: ('0'..'9');
FORALL: 'forall';
EXISTS: 'exists';
COLON: ':';
COMMA: ',';
DEFINE: 'define


TYPE_INT: 'Int';
TYPE_BOOL: 'Bool';
TYPE_REAL: 'Real';

WS: [ \t\r\n] -> skip;