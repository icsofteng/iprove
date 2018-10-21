grammar Propositional;
compilationUnit: stmt*;
stmt:
    assignStmt
    | invocationStmt
;
assignStmt: SET ID TO expr;
invocationStmt: name=ID ((expr COMMA)* expr)?;
expr: ID | INT | STRING;
COMMA: ',';
SAY: 'say';
SET: 'set';
TO: 'to';
INT: [0-9]+;
STRING: '"' (~('\n' | '"'))* '"';
ID: [a-zA-Z_] [a-zA-Z0-9_]*;