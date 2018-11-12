// Generated from src/parser/iProve.g4 by ANTLR 4.7.1
// jshint ignore: start
var antlr4 = require('antlr4/index');
var iProveListener = require('./iProveListener').iProveListener;
var iProveVisitor = require('./iProveVisitor').iProveVisitor;

var grammarFileName = "iProve.g4";

var serializedATN = ["\u0003\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964",
    "\u0003\'\u008d\u0004\u0002\t\u0002\u0004\u0003\t\u0003\u0004\u0004\t",
    "\u0004\u0004\u0005\t\u0005\u0003\u0002\u0003\u0002\u0003\u0003\u0003",
    "\u0003\u0005\u0003\u000f\n\u0003\u0003\u0004\u0003\u0004\u0003\u0004",
    "\u0005\u0004\u0014\n\u0004\u0003\u0005\u0003\u0005\u0003\u0005\u0003",
    "\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003",
    "\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003",
    "\u0005\u0007\u0005&\n\u0005\f\u0005\u000e\u0005)\u000b\u0005\u0005\u0005",
    "+\n\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005",
    "\u0003\u0005\u0003\u0005\u0003\u0005\u0007\u00055\n\u0005\f\u0005\u000e",
    "\u00058\u000b\u0005\u0005\u0005:\n\u0005\u0003\u0005\u0003\u0005\u0003",
    "\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003",
    "\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0007\u0005I",
    "\n\u0005\f\u0005\u000e\u0005L\u000b\u0005\u0003\u0005\u0003\u0005\u0003",
    "\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0007\u0005T\n\u0005\f\u0005",
    "\u000e\u0005W\u000b\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0005",
    "\u0005\\\n\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003",
    "\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003",
    "\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003",
    "\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003",
    "\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003",
    "\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003",
    "\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003",
    "\u0005\u0003\u0005\u0007\u0005\u0088\n\u0005\f\u0005\u000e\u0005\u008b",
    "\u000b\u0005\u0003\u0005\u0002\u0003\b\u0006\u0002\u0004\u0006\b\u0002",
    "\u0004\u0003\u0002\u000b\r\u0003\u0002\u000e\u0010\u0002\u00ab\u0002",
    "\n\u0003\u0002\u0002\u0002\u0004\u000e\u0003\u0002\u0002\u0002\u0006",
    "\u0010\u0003\u0002\u0002\u0002\b[\u0003\u0002\u0002\u0002\n\u000b\u0005",
    "\b\u0005\u0002\u000b\u0003\u0003\u0002\u0002\u0002\f\u000f\u0007\u0017",
    "\u0002\u0002\r\u000f\u0007\u0018\u0002\u0002\u000e\f\u0003\u0002\u0002",
    "\u0002\u000e\r\u0003\u0002\u0002\u0002\u000f\u0005\u0003\u0002\u0002",
    "\u0002\u0010\u0013\u0007\u0017\u0002\u0002\u0011\u0012\u0007\u001a\u0002",
    "\u0002\u0012\u0014\u0007\u0018\u0002\u0002\u0013\u0011\u0003\u0002\u0002",
    "\u0002\u0013\u0014\u0003\u0002\u0002\u0002\u0014\u0007\u0003\u0002\u0002",
    "\u0002\u0015\u0016\b\u0005\u0001\u0002\u0016\u0017\u0007\b\u0002\u0002",
    "\u0017\\\u0005\b\u0005\u001e\u0018\u0019\u0007\u0003\u0002\u0002\u0019",
    "\\\u0005\b\u0005\u001d\u001a\\\u0007\u0011\u0002\u0002\u001b\\\u0007",
    "\u0012\u0002\u0002\u001c\\\u0007\u0007\u0002\u0002\u001d\\\u0007\u001b",
    "\u0002\u0002\u001e\\\u0007\u001c\u0002\u0002\u001f \u0007\u0005\u0002",
    "\u0002 !\u0007\u0018\u0002\u0002!*\u0007\u0013\u0002\u0002\"\'\u0005",
    "\u0004\u0003\u0002#$\u0007\u0019\u0002\u0002$&\u0005\u0004\u0003\u0002",
    "%#\u0003\u0002\u0002\u0002&)\u0003\u0002\u0002\u0002\'%\u0003\u0002",
    "\u0002\u0002\'(\u0003\u0002\u0002\u0002(+\u0003\u0002\u0002\u0002)\'",
    "\u0003\u0002\u0002\u0002*\"\u0003\u0002\u0002\u0002*+\u0003\u0002\u0002",
    "\u0002+,\u0003\u0002\u0002\u0002,-\u0007\u0014\u0002\u0002-.\u0007\u001a",
    "\u0002\u0002.\\\u0007\u0018\u0002\u0002/0\u0007\u0018\u0002\u000209",
    "\u0007\u0013\u0002\u000216\u0005\u0004\u0003\u000223\u0007\u0019\u0002",
    "\u000235\u0005\u0004\u0003\u000242\u0003\u0002\u0002\u000258\u0003\u0002",
    "\u0002\u000264\u0003\u0002\u0002\u000267\u0003\u0002\u0002\u00027:\u0003",
    "\u0002\u0002\u000286\u0003\u0002\u0002\u000291\u0003\u0002\u0002\u0002",
    "9:\u0003\u0002\u0002\u0002:;\u0003\u0002\u0002\u0002;\\\u0007\u0014",
    "\u0002\u0002<=\u0007\u0013\u0002\u0002=>\u0005\b\u0005\u0002>?\u0007",
    "\u0014\u0002\u0002?\\\u0003\u0002\u0002\u0002@A\u0007\u0015\u0002\u0002",
    "AB\u0005\b\u0005\u0002BC\u0007\u0016\u0002\u0002C\\\u0003\u0002\u0002",
    "\u0002DE\u0007\u0004\u0002\u0002EJ\u0005\u0006\u0004\u0002FG\u0007\u0019",
    "\u0002\u0002GI\u0005\u0006\u0004\u0002HF\u0003\u0002\u0002\u0002IL\u0003",
    "\u0002\u0002\u0002JH\u0003\u0002\u0002\u0002JK\u0003\u0002\u0002\u0002",
    "KM\u0003\u0002\u0002\u0002LJ\u0003\u0002\u0002\u0002MN\u0005\b\u0005",
    "\u000fN\\\u0003\u0002\u0002\u0002OP\u0007\u0006\u0002\u0002PU\u0005",
    "\u0006\u0004\u0002QR\u0007\u0019\u0002\u0002RT\u0005\u0006\u0004\u0002",
    "SQ\u0003\u0002\u0002\u0002TW\u0003\u0002\u0002\u0002US\u0003\u0002\u0002",
    "\u0002UV\u0003\u0002\u0002\u0002VX\u0003\u0002\u0002\u0002WU\u0003\u0002",
    "\u0002\u0002XY\u0005\b\u0005\u000eY\\\u0003\u0002\u0002\u0002Z\\\u0007",
    "\u0018\u0002\u0002[\u0015\u0003\u0002\u0002\u0002[\u0018\u0003\u0002",
    "\u0002\u0002[\u001a\u0003\u0002\u0002\u0002[\u001b\u0003\u0002\u0002",
    "\u0002[\u001c\u0003\u0002\u0002\u0002[\u001d\u0003\u0002\u0002\u0002",
    "[\u001e\u0003\u0002\u0002\u0002[\u001f\u0003\u0002\u0002\u0002[/\u0003",
    "\u0002\u0002\u0002[<\u0003\u0002\u0002\u0002[@\u0003\u0002\u0002\u0002",
    "[D\u0003\u0002\u0002\u0002[O\u0003\u0002\u0002\u0002[Z\u0003\u0002\u0002",
    "\u0002\\\u0089\u0003\u0002\u0002\u0002]^\f\u001c\u0002\u0002^_\u0007",
    "\t\u0002\u0002_\u0088\u0005\b\u0005\u001d`a\f\u001b\u0002\u0002ab\u0007",
    "\n\u0002\u0002b\u0088\u0005\b\u0005\u001ccd\f\u001a\u0002\u0002de\t",
    "\u0002\u0002\u0002e\u0088\u0005\b\u0005\u001bfg\f\u0019\u0002\u0002",
    "gh\t\u0003\u0002\u0002h\u0088\u0005\b\u0005\u001aij\f\r\u0002\u0002",
    "jk\u0007$\u0002\u0002k\u0088\u0005\b\u0005\u000elm\f\f\u0002\u0002m",
    "n\u0007&\u0002\u0002n\u0088\u0005\b\u0005\rop\f\u000b\u0002\u0002pq",
    "\u0007%\u0002\u0002q\u0088\u0005\b\u0005\frs\f\n\u0002\u0002st\u0007",
    "\"\u0002\u0002t\u0088\u0005\b\u0005\u000buv\f\t\u0002\u0002vw\u0007",
    "#\u0002\u0002w\u0088\u0005\b\u0005\nxy\f\b\u0002\u0002yz\u0007\u001d",
    "\u0002\u0002z\u0088\u0005\b\u0005\t{|\f\u0007\u0002\u0002|}\u0007\u001e",
    "\u0002\u0002}\u0088\u0005\b\u0005\b~\u007f\f\u0006\u0002\u0002\u007f",
    "\u0080\u0007\u001f\u0002\u0002\u0080\u0088\u0005\b\u0005\u0007\u0081",
    "\u0082\f\u0005\u0002\u0002\u0082\u0083\u0007 \u0002\u0002\u0083\u0088",
    "\u0005\b\u0005\u0006\u0084\u0085\f\u0004\u0002\u0002\u0085\u0086\u0007",
    "!\u0002\u0002\u0086\u0088\u0005\b\u0005\u0005\u0087]\u0003\u0002\u0002",
    "\u0002\u0087`\u0003\u0002\u0002\u0002\u0087c\u0003\u0002\u0002\u0002",
    "\u0087f\u0003\u0002\u0002\u0002\u0087i\u0003\u0002\u0002\u0002\u0087",
    "l\u0003\u0002\u0002\u0002\u0087o\u0003\u0002\u0002\u0002\u0087r\u0003",
    "\u0002\u0002\u0002\u0087u\u0003\u0002\u0002\u0002\u0087x\u0003\u0002",
    "\u0002\u0002\u0087{\u0003\u0002\u0002\u0002\u0087~\u0003\u0002\u0002",
    "\u0002\u0087\u0081\u0003\u0002\u0002\u0002\u0087\u0084\u0003\u0002\u0002",
    "\u0002\u0088\u008b\u0003\u0002\u0002\u0002\u0089\u0087\u0003\u0002\u0002",
    "\u0002\u0089\u008a\u0003\u0002\u0002\u0002\u008a\t\u0003\u0002\u0002",
    "\u0002\u008b\u0089\u0003\u0002\u0002\u0002\r\u000e\u0013\'*69JU[\u0087",
    "\u0089"].join("");


var atn = new antlr4.atn.ATNDeserializer().deserialize(serializedATN);

var decisionsToDFA = atn.decisionToState.map( function(ds, index) { return new antlr4.dfa.DFA(ds, index); });

var sharedContextCache = new antlr4.PredictionContextCache();

var literalNames = [ null, "'assume'", "'forall'", "'define'", "'exists'", 
                     "'exit'", "'not'", "'and'", "'or'", "'implies'", "'=>'", 
                     "'->'", "'iff'", "'<=>'", "'<->'", "'true'", "'false'", 
                     "'('", "')'", "'['", "']'", null, null, "','", "':'", 
                     null, null, "'<'", "'<='", "'>'", "'>='", "'=='", "'+'", 
                     "'-'", "'^'", "'*'", "'/'" ];

var symbolicNames = [ null, "ASSUME", "FORALL", "DEFINE", "EXISTS", "EXIT", 
                      "NOT", "AND", "OR", "IMPLIES", "IMPLIES2", "IMPLIES3", 
                      "IFF", "IFF2", "IFF3", "TRUE", "FALSE", "BRACKET_OPEN", 
                      "BRACKET_CLOSE", "SQ_BRACKET_OPEN", "SQ_BRACKET_CLOSE", 
                      "VARIABLE", "IDENTIFIER", "COMMA", "COLON", "INTEGER", 
                      "REAL", "LESSTHAN", "LESSTHANEQ", "GREATERTHAN", "GREATERTHANEQ", 
                      "DOUBLEEQUALS", "PLUS", "MINUS", "POWER", "MULTIPLY", 
                      "DIVIDE", "WS" ];

var ruleNames =  [ "statement", "parameter", "variableDef", "expression" ];

function iProveParser (input) {
	antlr4.Parser.call(this, input);
    this._interp = new antlr4.atn.ParserATNSimulator(this, atn, decisionsToDFA, sharedContextCache);
    this.ruleNames = ruleNames;
    this.literalNames = literalNames;
    this.symbolicNames = symbolicNames;
    return this;
}

iProveParser.prototype = Object.create(antlr4.Parser.prototype);
iProveParser.prototype.constructor = iProveParser;

Object.defineProperty(iProveParser.prototype, "atn", {
	get : function() {
		return atn;
	}
});

iProveParser.EOF = antlr4.Token.EOF;
iProveParser.ASSUME = 1;
iProveParser.FORALL = 2;
iProveParser.DEFINE = 3;
iProveParser.EXISTS = 4;
iProveParser.EXIT = 5;
iProveParser.NOT = 6;
iProveParser.AND = 7;
iProveParser.OR = 8;
iProveParser.IMPLIES = 9;
iProveParser.IMPLIES2 = 10;
iProveParser.IMPLIES3 = 11;
iProveParser.IFF = 12;
iProveParser.IFF2 = 13;
iProveParser.IFF3 = 14;
iProveParser.TRUE = 15;
iProveParser.FALSE = 16;
iProveParser.BRACKET_OPEN = 17;
iProveParser.BRACKET_CLOSE = 18;
iProveParser.SQ_BRACKET_OPEN = 19;
iProveParser.SQ_BRACKET_CLOSE = 20;
iProveParser.VARIABLE = 21;
iProveParser.IDENTIFIER = 22;
iProveParser.COMMA = 23;
iProveParser.COLON = 24;
iProveParser.INTEGER = 25;
iProveParser.REAL = 26;
iProveParser.LESSTHAN = 27;
iProveParser.LESSTHANEQ = 28;
iProveParser.GREATERTHAN = 29;
iProveParser.GREATERTHANEQ = 30;
iProveParser.DOUBLEEQUALS = 31;
iProveParser.PLUS = 32;
iProveParser.MINUS = 33;
iProveParser.POWER = 34;
iProveParser.MULTIPLY = 35;
iProveParser.DIVIDE = 36;
iProveParser.WS = 37;

iProveParser.RULE_statement = 0;
iProveParser.RULE_parameter = 1;
iProveParser.RULE_variableDef = 2;
iProveParser.RULE_expression = 3;

function StatementContext(parser, parent, invokingState) {
	if(parent===undefined) {
	    parent = null;
	}
	if(invokingState===undefined || invokingState===null) {
		invokingState = -1;
	}
	antlr4.ParserRuleContext.call(this, parent, invokingState);
    this.parser = parser;
    this.ruleIndex = iProveParser.RULE_statement;
    return this;
}

StatementContext.prototype = Object.create(antlr4.ParserRuleContext.prototype);
StatementContext.prototype.constructor = StatementContext;

StatementContext.prototype.expression = function() {
    return this.getTypedRuleContext(ExpressionContext,0);
};

StatementContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterStatement(this);
	}
};

StatementContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitStatement(this);
	}
};

StatementContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitStatement(this);
    } else {
        return visitor.visitChildren(this);
    }
};




iProveParser.StatementContext = StatementContext;

iProveParser.prototype.statement = function() {

    var localctx = new StatementContext(this, this._ctx, this.state);
    this.enterRule(localctx, 0, iProveParser.RULE_statement);
    try {
        this.enterOuterAlt(localctx, 1);
        this.state = 8;
        this.expression(0);
    } catch (re) {
    	if(re instanceof antlr4.error.RecognitionException) {
	        localctx.exception = re;
	        this._errHandler.reportError(this, re);
	        this._errHandler.recover(this, re);
	    } else {
	    	throw re;
	    }
    } finally {
        this.exitRule();
    }
    return localctx;
};

function ParameterContext(parser, parent, invokingState) {
	if(parent===undefined) {
	    parent = null;
	}
	if(invokingState===undefined || invokingState===null) {
		invokingState = -1;
	}
	antlr4.ParserRuleContext.call(this, parent, invokingState);
    this.parser = parser;
    this.ruleIndex = iProveParser.RULE_parameter;
    return this;
}

ParameterContext.prototype = Object.create(antlr4.ParserRuleContext.prototype);
ParameterContext.prototype.constructor = ParameterContext;


 
ParameterContext.prototype.copyFrom = function(ctx) {
    antlr4.ParserRuleContext.prototype.copyFrom.call(this, ctx);
};


function ParamIdentContext(parser, ctx) {
	ParameterContext.call(this, parser);
    ParameterContext.prototype.copyFrom.call(this, ctx);
    return this;
}

ParamIdentContext.prototype = Object.create(ParameterContext.prototype);
ParamIdentContext.prototype.constructor = ParamIdentContext;

iProveParser.ParamIdentContext = ParamIdentContext;

ParamIdentContext.prototype.IDENTIFIER = function() {
    return this.getToken(iProveParser.IDENTIFIER, 0);
};
ParamIdentContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterParamIdent(this);
	}
};

ParamIdentContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitParamIdent(this);
	}
};

ParamIdentContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitParamIdent(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function ParamVarContext(parser, ctx) {
	ParameterContext.call(this, parser);
    ParameterContext.prototype.copyFrom.call(this, ctx);
    return this;
}

ParamVarContext.prototype = Object.create(ParameterContext.prototype);
ParamVarContext.prototype.constructor = ParamVarContext;

iProveParser.ParamVarContext = ParamVarContext;

ParamVarContext.prototype.VARIABLE = function() {
    return this.getToken(iProveParser.VARIABLE, 0);
};
ParamVarContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterParamVar(this);
	}
};

ParamVarContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitParamVar(this);
	}
};

ParamVarContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitParamVar(this);
    } else {
        return visitor.visitChildren(this);
    }
};



iProveParser.ParameterContext = ParameterContext;

iProveParser.prototype.parameter = function() {

    var localctx = new ParameterContext(this, this._ctx, this.state);
    this.enterRule(localctx, 2, iProveParser.RULE_parameter);
    try {
        this.state = 12;
        this._errHandler.sync(this);
        switch(this._input.LA(1)) {
        case iProveParser.VARIABLE:
            localctx = new ParamVarContext(this, localctx);
            this.enterOuterAlt(localctx, 1);
            this.state = 10;
            this.match(iProveParser.VARIABLE);
            break;
        case iProveParser.IDENTIFIER:
            localctx = new ParamIdentContext(this, localctx);
            this.enterOuterAlt(localctx, 2);
            this.state = 11;
            this.match(iProveParser.IDENTIFIER);
            break;
        default:
            throw new antlr4.error.NoViableAltException(this);
        }
    } catch (re) {
    	if(re instanceof antlr4.error.RecognitionException) {
	        localctx.exception = re;
	        this._errHandler.reportError(this, re);
	        this._errHandler.recover(this, re);
	    } else {
	    	throw re;
	    }
    } finally {
        this.exitRule();
    }
    return localctx;
};

function VariableDefContext(parser, parent, invokingState) {
	if(parent===undefined) {
	    parent = null;
	}
	if(invokingState===undefined || invokingState===null) {
		invokingState = -1;
	}
	antlr4.ParserRuleContext.call(this, parent, invokingState);
    this.parser = parser;
    this.ruleIndex = iProveParser.RULE_variableDef;
    return this;
}

VariableDefContext.prototype = Object.create(antlr4.ParserRuleContext.prototype);
VariableDefContext.prototype.constructor = VariableDefContext;

VariableDefContext.prototype.VARIABLE = function() {
    return this.getToken(iProveParser.VARIABLE, 0);
};

VariableDefContext.prototype.COLON = function() {
    return this.getToken(iProveParser.COLON, 0);
};

VariableDefContext.prototype.IDENTIFIER = function() {
    return this.getToken(iProveParser.IDENTIFIER, 0);
};

VariableDefContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterVariableDef(this);
	}
};

VariableDefContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitVariableDef(this);
	}
};

VariableDefContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitVariableDef(this);
    } else {
        return visitor.visitChildren(this);
    }
};




iProveParser.VariableDefContext = VariableDefContext;

iProveParser.prototype.variableDef = function() {

    var localctx = new VariableDefContext(this, this._ctx, this.state);
    this.enterRule(localctx, 4, iProveParser.RULE_variableDef);
    var _la = 0; // Token type
    try {
        this.enterOuterAlt(localctx, 1);
        this.state = 14;
        this.match(iProveParser.VARIABLE);
        this.state = 17;
        this._errHandler.sync(this);
        _la = this._input.LA(1);
        if(_la===iProveParser.COLON) {
            this.state = 15;
            this.match(iProveParser.COLON);
            this.state = 16;
            this.match(iProveParser.IDENTIFIER);
        }

    } catch (re) {
    	if(re instanceof antlr4.error.RecognitionException) {
	        localctx.exception = re;
	        this._errHandler.reportError(this, re);
	        this._errHandler.recover(this, re);
	    } else {
	    	throw re;
	    }
    } finally {
        this.exitRule();
    }
    return localctx;
};

function ExpressionContext(parser, parent, invokingState) {
	if(parent===undefined) {
	    parent = null;
	}
	if(invokingState===undefined || invokingState===null) {
		invokingState = -1;
	}
	antlr4.ParserRuleContext.call(this, parent, invokingState);
    this.parser = parser;
    this.ruleIndex = iProveParser.RULE_expression;
    return this;
}

ExpressionContext.prototype = Object.create(antlr4.ParserRuleContext.prototype);
ExpressionContext.prototype.constructor = ExpressionContext;


 
ExpressionContext.prototype.copyFrom = function(ctx) {
    antlr4.ParserRuleContext.prototype.copyFrom.call(this, ctx);
};

function AndExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

AndExpContext.prototype = Object.create(ExpressionContext.prototype);
AndExpContext.prototype.constructor = AndExpContext;

iProveParser.AndExpContext = AndExpContext;

AndExpContext.prototype.expression = function(i) {
    if(i===undefined) {
        i = null;
    }
    if(i===null) {
        return this.getTypedRuleContexts(ExpressionContext);
    } else {
        return this.getTypedRuleContext(ExpressionContext,i);
    }
};

AndExpContext.prototype.AND = function() {
    return this.getToken(iProveParser.AND, 0);
};
AndExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterAndExp(this);
	}
};

AndExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitAndExp(this);
	}
};

AndExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitAndExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function LessThanExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

LessThanExpContext.prototype = Object.create(ExpressionContext.prototype);
LessThanExpContext.prototype.constructor = LessThanExpContext;

iProveParser.LessThanExpContext = LessThanExpContext;

LessThanExpContext.prototype.expression = function(i) {
    if(i===undefined) {
        i = null;
    }
    if(i===null) {
        return this.getTypedRuleContexts(ExpressionContext);
    } else {
        return this.getTypedRuleContext(ExpressionContext,i);
    }
};

LessThanExpContext.prototype.LESSTHAN = function() {
    return this.getToken(iProveParser.LESSTHAN, 0);
};
LessThanExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterLessThanExp(this);
	}
};

LessThanExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitLessThanExp(this);
	}
};

LessThanExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitLessThanExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function ParenthesesExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

ParenthesesExpContext.prototype = Object.create(ExpressionContext.prototype);
ParenthesesExpContext.prototype.constructor = ParenthesesExpContext;

iProveParser.ParenthesesExpContext = ParenthesesExpContext;

ParenthesesExpContext.prototype.BRACKET_OPEN = function() {
    return this.getToken(iProveParser.BRACKET_OPEN, 0);
};

ParenthesesExpContext.prototype.expression = function() {
    return this.getTypedRuleContext(ExpressionContext,0);
};

ParenthesesExpContext.prototype.BRACKET_CLOSE = function() {
    return this.getToken(iProveParser.BRACKET_CLOSE, 0);
};
ParenthesesExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterParenthesesExp(this);
	}
};

ParenthesesExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitParenthesesExp(this);
	}
};

ParenthesesExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitParenthesesExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function AssumeExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

AssumeExpContext.prototype = Object.create(ExpressionContext.prototype);
AssumeExpContext.prototype.constructor = AssumeExpContext;

iProveParser.AssumeExpContext = AssumeExpContext;

AssumeExpContext.prototype.ASSUME = function() {
    return this.getToken(iProveParser.ASSUME, 0);
};

AssumeExpContext.prototype.expression = function() {
    return this.getTypedRuleContext(ExpressionContext,0);
};
AssumeExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterAssumeExp(this);
	}
};

AssumeExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitAssumeExp(this);
	}
};

AssumeExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitAssumeExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function ExitExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

ExitExpContext.prototype = Object.create(ExpressionContext.prototype);
ExitExpContext.prototype.constructor = ExitExpContext;

iProveParser.ExitExpContext = ExitExpContext;

ExitExpContext.prototype.EXIT = function() {
    return this.getToken(iProveParser.EXIT, 0);
};
ExitExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterExitExp(this);
	}
};

ExitExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitExitExp(this);
	}
};

ExitExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitExitExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function PlusExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

PlusExpContext.prototype = Object.create(ExpressionContext.prototype);
PlusExpContext.prototype.constructor = PlusExpContext;

iProveParser.PlusExpContext = PlusExpContext;

PlusExpContext.prototype.expression = function(i) {
    if(i===undefined) {
        i = null;
    }
    if(i===null) {
        return this.getTypedRuleContexts(ExpressionContext);
    } else {
        return this.getTypedRuleContext(ExpressionContext,i);
    }
};

PlusExpContext.prototype.PLUS = function() {
    return this.getToken(iProveParser.PLUS, 0);
};
PlusExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterPlusExp(this);
	}
};

PlusExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitPlusExp(this);
	}
};

PlusExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitPlusExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function RelationDefExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

RelationDefExpContext.prototype = Object.create(ExpressionContext.prototype);
RelationDefExpContext.prototype.constructor = RelationDefExpContext;

iProveParser.RelationDefExpContext = RelationDefExpContext;

RelationDefExpContext.prototype.DEFINE = function() {
    return this.getToken(iProveParser.DEFINE, 0);
};

RelationDefExpContext.prototype.IDENTIFIER = function(i) {
	if(i===undefined) {
		i = null;
	}
    if(i===null) {
        return this.getTokens(iProveParser.IDENTIFIER);
    } else {
        return this.getToken(iProveParser.IDENTIFIER, i);
    }
};


RelationDefExpContext.prototype.BRACKET_OPEN = function() {
    return this.getToken(iProveParser.BRACKET_OPEN, 0);
};

RelationDefExpContext.prototype.BRACKET_CLOSE = function() {
    return this.getToken(iProveParser.BRACKET_CLOSE, 0);
};

RelationDefExpContext.prototype.COLON = function() {
    return this.getToken(iProveParser.COLON, 0);
};

RelationDefExpContext.prototype.parameter = function(i) {
    if(i===undefined) {
        i = null;
    }
    if(i===null) {
        return this.getTypedRuleContexts(ParameterContext);
    } else {
        return this.getTypedRuleContext(ParameterContext,i);
    }
};

RelationDefExpContext.prototype.COMMA = function(i) {
	if(i===undefined) {
		i = null;
	}
    if(i===null) {
        return this.getTokens(iProveParser.COMMA);
    } else {
        return this.getToken(iProveParser.COMMA, i);
    }
};

RelationDefExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterRelationDefExp(this);
	}
};

RelationDefExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitRelationDefExp(this);
	}
};

RelationDefExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitRelationDefExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function GreaterThanEqExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

GreaterThanEqExpContext.prototype = Object.create(ExpressionContext.prototype);
GreaterThanEqExpContext.prototype.constructor = GreaterThanEqExpContext;

iProveParser.GreaterThanEqExpContext = GreaterThanEqExpContext;

GreaterThanEqExpContext.prototype.expression = function(i) {
    if(i===undefined) {
        i = null;
    }
    if(i===null) {
        return this.getTypedRuleContexts(ExpressionContext);
    } else {
        return this.getTypedRuleContext(ExpressionContext,i);
    }
};

GreaterThanEqExpContext.prototype.GREATERTHANEQ = function() {
    return this.getToken(iProveParser.GREATERTHANEQ, 0);
};
GreaterThanEqExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterGreaterThanEqExp(this);
	}
};

GreaterThanEqExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitGreaterThanEqExp(this);
	}
};

GreaterThanEqExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitGreaterThanEqExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function NotExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

NotExpContext.prototype = Object.create(ExpressionContext.prototype);
NotExpContext.prototype.constructor = NotExpContext;

iProveParser.NotExpContext = NotExpContext;

NotExpContext.prototype.NOT = function() {
    return this.getToken(iProveParser.NOT, 0);
};

NotExpContext.prototype.expression = function() {
    return this.getTypedRuleContext(ExpressionContext,0);
};
NotExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterNotExp(this);
	}
};

NotExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitNotExp(this);
	}
};

NotExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitNotExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function IffExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

IffExpContext.prototype = Object.create(ExpressionContext.prototype);
IffExpContext.prototype.constructor = IffExpContext;

iProveParser.IffExpContext = IffExpContext;

IffExpContext.prototype.expression = function(i) {
    if(i===undefined) {
        i = null;
    }
    if(i===null) {
        return this.getTypedRuleContexts(ExpressionContext);
    } else {
        return this.getTypedRuleContext(ExpressionContext,i);
    }
};

IffExpContext.prototype.IFF = function() {
    return this.getToken(iProveParser.IFF, 0);
};

IffExpContext.prototype.IFF2 = function() {
    return this.getToken(iProveParser.IFF2, 0);
};

IffExpContext.prototype.IFF3 = function() {
    return this.getToken(iProveParser.IFF3, 0);
};
IffExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterIffExp(this);
	}
};

IffExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitIffExp(this);
	}
};

IffExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitIffExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function GreaterThanExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

GreaterThanExpContext.prototype = Object.create(ExpressionContext.prototype);
GreaterThanExpContext.prototype.constructor = GreaterThanExpContext;

iProveParser.GreaterThanExpContext = GreaterThanExpContext;

GreaterThanExpContext.prototype.expression = function(i) {
    if(i===undefined) {
        i = null;
    }
    if(i===null) {
        return this.getTypedRuleContexts(ExpressionContext);
    } else {
        return this.getTypedRuleContext(ExpressionContext,i);
    }
};

GreaterThanExpContext.prototype.GREATERTHAN = function() {
    return this.getToken(iProveParser.GREATERTHAN, 0);
};
GreaterThanExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterGreaterThanExp(this);
	}
};

GreaterThanExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitGreaterThanExp(this);
	}
};

GreaterThanExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitGreaterThanExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function RelationExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

RelationExpContext.prototype = Object.create(ExpressionContext.prototype);
RelationExpContext.prototype.constructor = RelationExpContext;

iProveParser.RelationExpContext = RelationExpContext;

RelationExpContext.prototype.IDENTIFIER = function() {
    return this.getToken(iProveParser.IDENTIFIER, 0);
};

RelationExpContext.prototype.BRACKET_OPEN = function() {
    return this.getToken(iProveParser.BRACKET_OPEN, 0);
};

RelationExpContext.prototype.BRACKET_CLOSE = function() {
    return this.getToken(iProveParser.BRACKET_CLOSE, 0);
};

RelationExpContext.prototype.parameter = function(i) {
    if(i===undefined) {
        i = null;
    }
    if(i===null) {
        return this.getTypedRuleContexts(ParameterContext);
    } else {
        return this.getTypedRuleContext(ParameterContext,i);
    }
};

RelationExpContext.prototype.COMMA = function(i) {
	if(i===undefined) {
		i = null;
	}
    if(i===null) {
        return this.getTokens(iProveParser.COMMA);
    } else {
        return this.getToken(iProveParser.COMMA, i);
    }
};

RelationExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterRelationExp(this);
	}
};

RelationExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitRelationExp(this);
	}
};

RelationExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitRelationExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function ForallExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

ForallExpContext.prototype = Object.create(ExpressionContext.prototype);
ForallExpContext.prototype.constructor = ForallExpContext;

iProveParser.ForallExpContext = ForallExpContext;

ForallExpContext.prototype.FORALL = function() {
    return this.getToken(iProveParser.FORALL, 0);
};

ForallExpContext.prototype.variableDef = function(i) {
    if(i===undefined) {
        i = null;
    }
    if(i===null) {
        return this.getTypedRuleContexts(VariableDefContext);
    } else {
        return this.getTypedRuleContext(VariableDefContext,i);
    }
};

ForallExpContext.prototype.expression = function() {
    return this.getTypedRuleContext(ExpressionContext,0);
};

ForallExpContext.prototype.COMMA = function(i) {
	if(i===undefined) {
		i = null;
	}
    if(i===null) {
        return this.getTokens(iProveParser.COMMA);
    } else {
        return this.getToken(iProveParser.COMMA, i);
    }
};

ForallExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterForallExp(this);
	}
};

ForallExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitForallExp(this);
	}
};

ForallExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitForallExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function LiteralExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

LiteralExpContext.prototype = Object.create(ExpressionContext.prototype);
LiteralExpContext.prototype.constructor = LiteralExpContext;

iProveParser.LiteralExpContext = LiteralExpContext;

LiteralExpContext.prototype.IDENTIFIER = function() {
    return this.getToken(iProveParser.IDENTIFIER, 0);
};
LiteralExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterLiteralExp(this);
	}
};

LiteralExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitLiteralExp(this);
	}
};

LiteralExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitLiteralExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function IntegerExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

IntegerExpContext.prototype = Object.create(ExpressionContext.prototype);
IntegerExpContext.prototype.constructor = IntegerExpContext;

iProveParser.IntegerExpContext = IntegerExpContext;

IntegerExpContext.prototype.INTEGER = function() {
    return this.getToken(iProveParser.INTEGER, 0);
};
IntegerExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterIntegerExp(this);
	}
};

IntegerExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitIntegerExp(this);
	}
};

IntegerExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitIntegerExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function TrueExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

TrueExpContext.prototype = Object.create(ExpressionContext.prototype);
TrueExpContext.prototype.constructor = TrueExpContext;

iProveParser.TrueExpContext = TrueExpContext;

TrueExpContext.prototype.TRUE = function() {
    return this.getToken(iProveParser.TRUE, 0);
};
TrueExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterTrueExp(this);
	}
};

TrueExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitTrueExp(this);
	}
};

TrueExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitTrueExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function MultiplyExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

MultiplyExpContext.prototype = Object.create(ExpressionContext.prototype);
MultiplyExpContext.prototype.constructor = MultiplyExpContext;

iProveParser.MultiplyExpContext = MultiplyExpContext;

MultiplyExpContext.prototype.expression = function(i) {
    if(i===undefined) {
        i = null;
    }
    if(i===null) {
        return this.getTypedRuleContexts(ExpressionContext);
    } else {
        return this.getTypedRuleContext(ExpressionContext,i);
    }
};

MultiplyExpContext.prototype.MULTIPLY = function() {
    return this.getToken(iProveParser.MULTIPLY, 0);
};
MultiplyExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterMultiplyExp(this);
	}
};

MultiplyExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitMultiplyExp(this);
	}
};

MultiplyExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitMultiplyExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function MinusExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

MinusExpContext.prototype = Object.create(ExpressionContext.prototype);
MinusExpContext.prototype.constructor = MinusExpContext;

iProveParser.MinusExpContext = MinusExpContext;

MinusExpContext.prototype.expression = function(i) {
    if(i===undefined) {
        i = null;
    }
    if(i===null) {
        return this.getTypedRuleContexts(ExpressionContext);
    } else {
        return this.getTypedRuleContext(ExpressionContext,i);
    }
};

MinusExpContext.prototype.MINUS = function() {
    return this.getToken(iProveParser.MINUS, 0);
};
MinusExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterMinusExp(this);
	}
};

MinusExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitMinusExp(this);
	}
};

MinusExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitMinusExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function OrExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

OrExpContext.prototype = Object.create(ExpressionContext.prototype);
OrExpContext.prototype.constructor = OrExpContext;

iProveParser.OrExpContext = OrExpContext;

OrExpContext.prototype.expression = function(i) {
    if(i===undefined) {
        i = null;
    }
    if(i===null) {
        return this.getTypedRuleContexts(ExpressionContext);
    } else {
        return this.getTypedRuleContext(ExpressionContext,i);
    }
};

OrExpContext.prototype.OR = function() {
    return this.getToken(iProveParser.OR, 0);
};
OrExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterOrExp(this);
	}
};

OrExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitOrExp(this);
	}
};

OrExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitOrExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function SqParenthesesExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

SqParenthesesExpContext.prototype = Object.create(ExpressionContext.prototype);
SqParenthesesExpContext.prototype.constructor = SqParenthesesExpContext;

iProveParser.SqParenthesesExpContext = SqParenthesesExpContext;

SqParenthesesExpContext.prototype.SQ_BRACKET_OPEN = function() {
    return this.getToken(iProveParser.SQ_BRACKET_OPEN, 0);
};

SqParenthesesExpContext.prototype.expression = function() {
    return this.getTypedRuleContext(ExpressionContext,0);
};

SqParenthesesExpContext.prototype.SQ_BRACKET_CLOSE = function() {
    return this.getToken(iProveParser.SQ_BRACKET_CLOSE, 0);
};
SqParenthesesExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterSqParenthesesExp(this);
	}
};

SqParenthesesExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitSqParenthesesExp(this);
	}
};

SqParenthesesExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitSqParenthesesExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function LessThanEqExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

LessThanEqExpContext.prototype = Object.create(ExpressionContext.prototype);
LessThanEqExpContext.prototype.constructor = LessThanEqExpContext;

iProveParser.LessThanEqExpContext = LessThanEqExpContext;

LessThanEqExpContext.prototype.expression = function(i) {
    if(i===undefined) {
        i = null;
    }
    if(i===null) {
        return this.getTypedRuleContexts(ExpressionContext);
    } else {
        return this.getTypedRuleContext(ExpressionContext,i);
    }
};

LessThanEqExpContext.prototype.LESSTHANEQ = function() {
    return this.getToken(iProveParser.LESSTHANEQ, 0);
};
LessThanEqExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterLessThanEqExp(this);
	}
};

LessThanEqExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitLessThanEqExp(this);
	}
};

LessThanEqExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitLessThanEqExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function EqualExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

EqualExpContext.prototype = Object.create(ExpressionContext.prototype);
EqualExpContext.prototype.constructor = EqualExpContext;

iProveParser.EqualExpContext = EqualExpContext;

EqualExpContext.prototype.expression = function(i) {
    if(i===undefined) {
        i = null;
    }
    if(i===null) {
        return this.getTypedRuleContexts(ExpressionContext);
    } else {
        return this.getTypedRuleContext(ExpressionContext,i);
    }
};

EqualExpContext.prototype.DOUBLEEQUALS = function() {
    return this.getToken(iProveParser.DOUBLEEQUALS, 0);
};
EqualExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterEqualExp(this);
	}
};

EqualExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitEqualExp(this);
	}
};

EqualExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitEqualExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function ExistsExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

ExistsExpContext.prototype = Object.create(ExpressionContext.prototype);
ExistsExpContext.prototype.constructor = ExistsExpContext;

iProveParser.ExistsExpContext = ExistsExpContext;

ExistsExpContext.prototype.EXISTS = function() {
    return this.getToken(iProveParser.EXISTS, 0);
};

ExistsExpContext.prototype.variableDef = function(i) {
    if(i===undefined) {
        i = null;
    }
    if(i===null) {
        return this.getTypedRuleContexts(VariableDefContext);
    } else {
        return this.getTypedRuleContext(VariableDefContext,i);
    }
};

ExistsExpContext.prototype.expression = function() {
    return this.getTypedRuleContext(ExpressionContext,0);
};

ExistsExpContext.prototype.COMMA = function(i) {
	if(i===undefined) {
		i = null;
	}
    if(i===null) {
        return this.getTokens(iProveParser.COMMA);
    } else {
        return this.getToken(iProveParser.COMMA, i);
    }
};

ExistsExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterExistsExp(this);
	}
};

ExistsExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitExistsExp(this);
	}
};

ExistsExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitExistsExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function PowerExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

PowerExpContext.prototype = Object.create(ExpressionContext.prototype);
PowerExpContext.prototype.constructor = PowerExpContext;

iProveParser.PowerExpContext = PowerExpContext;

PowerExpContext.prototype.expression = function(i) {
    if(i===undefined) {
        i = null;
    }
    if(i===null) {
        return this.getTypedRuleContexts(ExpressionContext);
    } else {
        return this.getTypedRuleContext(ExpressionContext,i);
    }
};

PowerExpContext.prototype.POWER = function() {
    return this.getToken(iProveParser.POWER, 0);
};
PowerExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterPowerExp(this);
	}
};

PowerExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitPowerExp(this);
	}
};

PowerExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitPowerExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function RealExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

RealExpContext.prototype = Object.create(ExpressionContext.prototype);
RealExpContext.prototype.constructor = RealExpContext;

iProveParser.RealExpContext = RealExpContext;

RealExpContext.prototype.REAL = function() {
    return this.getToken(iProveParser.REAL, 0);
};
RealExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterRealExp(this);
	}
};

RealExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitRealExp(this);
	}
};

RealExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitRealExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function DivideExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

DivideExpContext.prototype = Object.create(ExpressionContext.prototype);
DivideExpContext.prototype.constructor = DivideExpContext;

iProveParser.DivideExpContext = DivideExpContext;

DivideExpContext.prototype.expression = function(i) {
    if(i===undefined) {
        i = null;
    }
    if(i===null) {
        return this.getTypedRuleContexts(ExpressionContext);
    } else {
        return this.getTypedRuleContext(ExpressionContext,i);
    }
};

DivideExpContext.prototype.DIVIDE = function() {
    return this.getToken(iProveParser.DIVIDE, 0);
};
DivideExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterDivideExp(this);
	}
};

DivideExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitDivideExp(this);
	}
};

DivideExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitDivideExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function FalseExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

FalseExpContext.prototype = Object.create(ExpressionContext.prototype);
FalseExpContext.prototype.constructor = FalseExpContext;

iProveParser.FalseExpContext = FalseExpContext;

FalseExpContext.prototype.FALSE = function() {
    return this.getToken(iProveParser.FALSE, 0);
};
FalseExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterFalseExp(this);
	}
};

FalseExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitFalseExp(this);
	}
};

FalseExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitFalseExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function ImpliesExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

ImpliesExpContext.prototype = Object.create(ExpressionContext.prototype);
ImpliesExpContext.prototype.constructor = ImpliesExpContext;

iProveParser.ImpliesExpContext = ImpliesExpContext;

ImpliesExpContext.prototype.expression = function(i) {
    if(i===undefined) {
        i = null;
    }
    if(i===null) {
        return this.getTypedRuleContexts(ExpressionContext);
    } else {
        return this.getTypedRuleContext(ExpressionContext,i);
    }
};

ImpliesExpContext.prototype.IMPLIES = function() {
    return this.getToken(iProveParser.IMPLIES, 0);
};

ImpliesExpContext.prototype.IMPLIES2 = function() {
    return this.getToken(iProveParser.IMPLIES2, 0);
};

ImpliesExpContext.prototype.IMPLIES3 = function() {
    return this.getToken(iProveParser.IMPLIES3, 0);
};
ImpliesExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterImpliesExp(this);
	}
};

ImpliesExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitImpliesExp(this);
	}
};

ImpliesExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitImpliesExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};



iProveParser.prototype.expression = function(_p) {
	if(_p===undefined) {
	    _p = 0;
	}
    var _parentctx = this._ctx;
    var _parentState = this.state;
    var localctx = new ExpressionContext(this, this._ctx, _parentState);
    var _prevctx = localctx;
    var _startState = 6;
    this.enterRecursionRule(localctx, 6, iProveParser.RULE_expression, _p);
    var _la = 0; // Token type
    try {
        this.enterOuterAlt(localctx, 1);
        this.state = 89;
        this._errHandler.sync(this);
        var la_ = this._interp.adaptivePredict(this._input,8,this._ctx);
        switch(la_) {
        case 1:
            localctx = new NotExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;

            this.state = 20;
            this.match(iProveParser.NOT);
            this.state = 21;
            this.expression(28);
            break;

        case 2:
            localctx = new AssumeExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 22;
            this.match(iProveParser.ASSUME);
            this.state = 23;
            this.expression(27);
            break;

        case 3:
            localctx = new TrueExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 24;
            this.match(iProveParser.TRUE);
            break;

        case 4:
            localctx = new FalseExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 25;
            this.match(iProveParser.FALSE);
            break;

        case 5:
            localctx = new ExitExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 26;
            this.match(iProveParser.EXIT);
            break;

        case 6:
            localctx = new IntegerExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 27;
            this.match(iProveParser.INTEGER);
            break;

        case 7:
            localctx = new RealExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 28;
            this.match(iProveParser.REAL);
            break;

        case 8:
            localctx = new RelationDefExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 29;
            this.match(iProveParser.DEFINE);
            this.state = 30;
            this.match(iProveParser.IDENTIFIER);
            this.state = 31;
            this.match(iProveParser.BRACKET_OPEN);
            this.state = 40;
            this._errHandler.sync(this);
            _la = this._input.LA(1);
            if(_la===iProveParser.VARIABLE || _la===iProveParser.IDENTIFIER) {
                this.state = 32;
                this.parameter();
                this.state = 37;
                this._errHandler.sync(this);
                _la = this._input.LA(1);
                while(_la===iProveParser.COMMA) {
                    this.state = 33;
                    this.match(iProveParser.COMMA);
                    this.state = 34;
                    this.parameter();
                    this.state = 39;
                    this._errHandler.sync(this);
                    _la = this._input.LA(1);
                }
            }

            this.state = 42;
            this.match(iProveParser.BRACKET_CLOSE);
            this.state = 43;
            this.match(iProveParser.COLON);
            this.state = 44;
            this.match(iProveParser.IDENTIFIER);
            break;

        case 9:
            localctx = new RelationExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 45;
            this.match(iProveParser.IDENTIFIER);
            this.state = 46;
            this.match(iProveParser.BRACKET_OPEN);
            this.state = 55;
            this._errHandler.sync(this);
            _la = this._input.LA(1);
            if(_la===iProveParser.VARIABLE || _la===iProveParser.IDENTIFIER) {
                this.state = 47;
                this.parameter();
                this.state = 52;
                this._errHandler.sync(this);
                _la = this._input.LA(1);
                while(_la===iProveParser.COMMA) {
                    this.state = 48;
                    this.match(iProveParser.COMMA);
                    this.state = 49;
                    this.parameter();
                    this.state = 54;
                    this._errHandler.sync(this);
                    _la = this._input.LA(1);
                }
            }

            this.state = 57;
            this.match(iProveParser.BRACKET_CLOSE);
            break;

        case 10:
            localctx = new ParenthesesExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 58;
            this.match(iProveParser.BRACKET_OPEN);
            this.state = 59;
            this.expression(0);
            this.state = 60;
            this.match(iProveParser.BRACKET_CLOSE);
            break;

        case 11:
            localctx = new SqParenthesesExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 62;
            this.match(iProveParser.SQ_BRACKET_OPEN);
            this.state = 63;
            this.expression(0);
            this.state = 64;
            this.match(iProveParser.SQ_BRACKET_CLOSE);
            break;

        case 12:
            localctx = new ForallExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 66;
            this.match(iProveParser.FORALL);
            this.state = 67;
            this.variableDef();
            this.state = 72;
            this._errHandler.sync(this);
            _la = this._input.LA(1);
            while(_la===iProveParser.COMMA) {
                this.state = 68;
                this.match(iProveParser.COMMA);
                this.state = 69;
                this.variableDef();
                this.state = 74;
                this._errHandler.sync(this);
                _la = this._input.LA(1);
            }
            this.state = 75;
            this.expression(13);
            break;

        case 13:
            localctx = new ExistsExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 77;
            this.match(iProveParser.EXISTS);
            this.state = 78;
            this.variableDef();
            this.state = 83;
            this._errHandler.sync(this);
            _la = this._input.LA(1);
            while(_la===iProveParser.COMMA) {
                this.state = 79;
                this.match(iProveParser.COMMA);
                this.state = 80;
                this.variableDef();
                this.state = 85;
                this._errHandler.sync(this);
                _la = this._input.LA(1);
            }
            this.state = 86;
            this.expression(12);
            break;

        case 14:
            localctx = new LiteralExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 88;
            this.match(iProveParser.IDENTIFIER);
            break;

        }
        this._ctx.stop = this._input.LT(-1);
        this.state = 135;
        this._errHandler.sync(this);
        var _alt = this._interp.adaptivePredict(this._input,10,this._ctx)
        while(_alt!=2 && _alt!=antlr4.atn.ATN.INVALID_ALT_NUMBER) {
            if(_alt===1) {
                if(this._parseListeners!==null) {
                    this.triggerExitRuleEvent();
                }
                _prevctx = localctx;
                this.state = 133;
                this._errHandler.sync(this);
                var la_ = this._interp.adaptivePredict(this._input,9,this._ctx);
                switch(la_) {
                case 1:
                    localctx = new AndExpContext(this, new ExpressionContext(this, _parentctx, _parentState));
                    this.pushNewRecursionContext(localctx, _startState, iProveParser.RULE_expression);
                    this.state = 91;
                    if (!( this.precpred(this._ctx, 26))) {
                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 26)");
                    }
                    this.state = 92;
                    this.match(iProveParser.AND);
                    this.state = 93;
                    this.expression(27);
                    break;

                case 2:
                    localctx = new OrExpContext(this, new ExpressionContext(this, _parentctx, _parentState));
                    this.pushNewRecursionContext(localctx, _startState, iProveParser.RULE_expression);
                    this.state = 94;
                    if (!( this.precpred(this._ctx, 25))) {
                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 25)");
                    }
                    this.state = 95;
                    this.match(iProveParser.OR);
                    this.state = 96;
                    this.expression(26);
                    break;

                case 3:
                    localctx = new ImpliesExpContext(this, new ExpressionContext(this, _parentctx, _parentState));
                    this.pushNewRecursionContext(localctx, _startState, iProveParser.RULE_expression);
                    this.state = 97;
                    if (!( this.precpred(this._ctx, 24))) {
                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 24)");
                    }
                    this.state = 98;
                    _la = this._input.LA(1);
                    if(!((((_la) & ~0x1f) == 0 && ((1 << _la) & ((1 << iProveParser.IMPLIES) | (1 << iProveParser.IMPLIES2) | (1 << iProveParser.IMPLIES3))) !== 0))) {
                    this._errHandler.recoverInline(this);
                    }
                    else {
                    	this._errHandler.reportMatch(this);
                        this.consume();
                    }
                    this.state = 99;
                    this.expression(25);
                    break;

                case 4:
                    localctx = new IffExpContext(this, new ExpressionContext(this, _parentctx, _parentState));
                    this.pushNewRecursionContext(localctx, _startState, iProveParser.RULE_expression);
                    this.state = 100;
                    if (!( this.precpred(this._ctx, 23))) {
                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 23)");
                    }
                    this.state = 101;
                    _la = this._input.LA(1);
                    if(!((((_la) & ~0x1f) == 0 && ((1 << _la) & ((1 << iProveParser.IFF) | (1 << iProveParser.IFF2) | (1 << iProveParser.IFF3))) !== 0))) {
                    this._errHandler.recoverInline(this);
                    }
                    else {
                    	this._errHandler.reportMatch(this);
                        this.consume();
                    }
                    this.state = 102;
                    this.expression(24);
                    break;

                case 5:
                    localctx = new PowerExpContext(this, new ExpressionContext(this, _parentctx, _parentState));
                    this.pushNewRecursionContext(localctx, _startState, iProveParser.RULE_expression);
                    this.state = 103;
                    if (!( this.precpred(this._ctx, 11))) {
                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 11)");
                    }
                    this.state = 104;
                    this.match(iProveParser.POWER);
                    this.state = 105;
                    this.expression(12);
                    break;

                case 6:
                    localctx = new DivideExpContext(this, new ExpressionContext(this, _parentctx, _parentState));
                    this.pushNewRecursionContext(localctx, _startState, iProveParser.RULE_expression);
                    this.state = 106;
                    if (!( this.precpred(this._ctx, 10))) {
                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 10)");
                    }
                    this.state = 107;
                    this.match(iProveParser.DIVIDE);
                    this.state = 108;
                    this.expression(11);
                    break;

                case 7:
                    localctx = new MultiplyExpContext(this, new ExpressionContext(this, _parentctx, _parentState));
                    this.pushNewRecursionContext(localctx, _startState, iProveParser.RULE_expression);
                    this.state = 109;
                    if (!( this.precpred(this._ctx, 9))) {
                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 9)");
                    }
                    this.state = 110;
                    this.match(iProveParser.MULTIPLY);
                    this.state = 111;
                    this.expression(10);
                    break;

                case 8:
                    localctx = new PlusExpContext(this, new ExpressionContext(this, _parentctx, _parentState));
                    this.pushNewRecursionContext(localctx, _startState, iProveParser.RULE_expression);
                    this.state = 112;
                    if (!( this.precpred(this._ctx, 8))) {
                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 8)");
                    }
                    this.state = 113;
                    this.match(iProveParser.PLUS);
                    this.state = 114;
                    this.expression(9);
                    break;

                case 9:
                    localctx = new MinusExpContext(this, new ExpressionContext(this, _parentctx, _parentState));
                    this.pushNewRecursionContext(localctx, _startState, iProveParser.RULE_expression);
                    this.state = 115;
                    if (!( this.precpred(this._ctx, 7))) {
                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 7)");
                    }
                    this.state = 116;
                    this.match(iProveParser.MINUS);
                    this.state = 117;
                    this.expression(8);
                    break;

                case 10:
                    localctx = new LessThanExpContext(this, new ExpressionContext(this, _parentctx, _parentState));
                    this.pushNewRecursionContext(localctx, _startState, iProveParser.RULE_expression);
                    this.state = 118;
                    if (!( this.precpred(this._ctx, 6))) {
                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 6)");
                    }
                    this.state = 119;
                    this.match(iProveParser.LESSTHAN);
                    this.state = 120;
                    this.expression(7);
                    break;

                case 11:
                    localctx = new LessThanEqExpContext(this, new ExpressionContext(this, _parentctx, _parentState));
                    this.pushNewRecursionContext(localctx, _startState, iProveParser.RULE_expression);
                    this.state = 121;
                    if (!( this.precpred(this._ctx, 5))) {
                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 5)");
                    }
                    this.state = 122;
                    this.match(iProveParser.LESSTHANEQ);
                    this.state = 123;
                    this.expression(6);
                    break;

                case 12:
                    localctx = new GreaterThanExpContext(this, new ExpressionContext(this, _parentctx, _parentState));
                    this.pushNewRecursionContext(localctx, _startState, iProveParser.RULE_expression);
                    this.state = 124;
                    if (!( this.precpred(this._ctx, 4))) {
                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 4)");
                    }
                    this.state = 125;
                    this.match(iProveParser.GREATERTHAN);
                    this.state = 126;
                    this.expression(5);
                    break;

                case 13:
                    localctx = new GreaterThanEqExpContext(this, new ExpressionContext(this, _parentctx, _parentState));
                    this.pushNewRecursionContext(localctx, _startState, iProveParser.RULE_expression);
                    this.state = 127;
                    if (!( this.precpred(this._ctx, 3))) {
                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 3)");
                    }
                    this.state = 128;
                    this.match(iProveParser.GREATERTHANEQ);
                    this.state = 129;
                    this.expression(4);
                    break;

                case 14:
                    localctx = new EqualExpContext(this, new ExpressionContext(this, _parentctx, _parentState));
                    this.pushNewRecursionContext(localctx, _startState, iProveParser.RULE_expression);
                    this.state = 130;
                    if (!( this.precpred(this._ctx, 2))) {
                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 2)");
                    }
                    this.state = 131;
                    this.match(iProveParser.DOUBLEEQUALS);
                    this.state = 132;
                    this.expression(3);
                    break;

                } 
            }
            this.state = 137;
            this._errHandler.sync(this);
            _alt = this._interp.adaptivePredict(this._input,10,this._ctx);
        }

    } catch( error) {
        if(error instanceof antlr4.error.RecognitionException) {
	        localctx.exception = error;
	        this._errHandler.reportError(this, error);
	        this._errHandler.recover(this, error);
	    } else {
	    	throw error;
	    }
    } finally {
        this.unrollRecursionContexts(_parentctx)
    }
    return localctx;
};


iProveParser.prototype.sempred = function(localctx, ruleIndex, predIndex) {
	switch(ruleIndex) {
	case 3:
			return this.expression_sempred(localctx, predIndex);
    default:
        throw "No predicate with index:" + ruleIndex;
   }
};

iProveParser.prototype.expression_sempred = function(localctx, predIndex) {
	switch(predIndex) {
		case 0:
			return this.precpred(this._ctx, 26);
		case 1:
			return this.precpred(this._ctx, 25);
		case 2:
			return this.precpred(this._ctx, 24);
		case 3:
			return this.precpred(this._ctx, 23);
		case 4:
			return this.precpred(this._ctx, 11);
		case 5:
			return this.precpred(this._ctx, 10);
		case 6:
			return this.precpred(this._ctx, 9);
		case 7:
			return this.precpred(this._ctx, 8);
		case 8:
			return this.precpred(this._ctx, 7);
		case 9:
			return this.precpred(this._ctx, 6);
		case 10:
			return this.precpred(this._ctx, 5);
		case 11:
			return this.precpred(this._ctx, 4);
		case 12:
			return this.precpred(this._ctx, 3);
		case 13:
			return this.precpred(this._ctx, 2);
		default:
			throw "No predicate with index:" + predIndex;
	}
};


exports.iProveParser = iProveParser;
