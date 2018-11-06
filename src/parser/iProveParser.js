// Generated from src/parser/iProve.g4 by ANTLR 4.7.1
// jshint ignore: start
var antlr4 = require('antlr4/index');
var iProveListener = require('./iProveListener').iProveListener;
var iProveVisitor = require('./iProveVisitor').iProveVisitor;

var grammarFileName = "iProve.g4";

var serializedATN = ["\u0003\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964",
    "\u0003\u001eO\u0004\u0002\t\u0002\u0004\u0003\t\u0003\u0004\u0004\t",
    "\u0004\u0004\u0005\t\u0005\u0003\u0002\u0003\u0002\u0003\u0003\u0003",
    "\u0003\u0005\u0003\u000f\n\u0003\u0003\u0004\u0003\u0004\u0003\u0004",
    "\u0003\u0004\u0003\u0004\u0007\u0004\u0016\n\u0004\f\u0004\u000e\u0004",
    "\u0019\u000b\u0004\u0005\u0004\u001b\n\u0004\u0003\u0004\u0003\u0004",
    "\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005",
    "\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005",
    "\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005",
    "\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005",
    "\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0005\u0005",
    "<\n\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005",
    "\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005",
    "\u0003\u0005\u0007\u0005J\n\u0005\f\u0005\u000e\u0005M\u000b\u0005\u0003",
    "\u0005\u0002\u0003\b\u0006\u0002\u0004\u0006\b\u0002\u0004\u0003\u0002",
    "\u000b\r\u0003\u0002\u000e\u0010\u0002\\\u0002\n\u0003\u0002\u0002\u0002",
    "\u0004\u000e\u0003\u0002\u0002\u0002\u0006\u0010\u0003\u0002\u0002\u0002",
    "\b;\u0003\u0002\u0002\u0002\n\u000b\u0005\b\u0005\u0002\u000b\u0003",
    "\u0003\u0002\u0002\u0002\f\u000f\u0007\u0018\u0002\u0002\r\u000f\u0007",
    "\u0019\u0002\u0002\u000e\f\u0003\u0002\u0002\u0002\u000e\r\u0003\u0002",
    "\u0002\u0002\u000f\u0005\u0003\u0002\u0002\u0002\u0010\u0011\u0007\u001a",
    "\u0002\u0002\u0011\u001a\u0007\u0013\u0002\u0002\u0012\u0017\u0005\u0004",
    "\u0003\u0002\u0013\u0014\u0007\u001c\u0002\u0002\u0014\u0016\u0005\u0004",
    "\u0003\u0002\u0015\u0013\u0003\u0002\u0002\u0002\u0016\u0019\u0003\u0002",
    "\u0002\u0002\u0017\u0015\u0003\u0002\u0002\u0002\u0017\u0018\u0003\u0002",
    "\u0002\u0002\u0018\u001b\u0003\u0002\u0002\u0002\u0019\u0017\u0003\u0002",
    "\u0002\u0002\u001a\u0012\u0003\u0002\u0002\u0002\u001a\u001b\u0003\u0002",
    "\u0002\u0002\u001b\u001c\u0003\u0002\u0002\u0002\u001c\u001d\u0007\u0014",
    "\u0002\u0002\u001d\u0007\u0003\u0002\u0002\u0002\u001e\u001f\b\u0005",
    "\u0001\u0002\u001f \u0007\b\u0002\u0002 <\u0005\b\u0005\u0012!\"\u0007",
    "\u0003\u0002\u0002\"<\u0005\b\u0005\u0011#<\u0007\u0017\u0002\u0002",
    "$<\u0007\u0011\u0002\u0002%<\u0007\u0012\u0002\u0002&<\u0007\u0007\u0002",
    "\u0002\'<\u0005\u0006\u0004\u0002()\u0007\u0013\u0002\u0002)*\u0005",
    "\b\u0005\u0002*+\u0007\u0014\u0002\u0002+<\u0003\u0002\u0002\u0002,",
    "-\u0007\u0015\u0002\u0002-.\u0005\b\u0005\u0002./\u0007\u0016\u0002",
    "\u0002/<\u0003\u0002\u0002\u000201\u0007\u0004\u0002\u000212\u0007\u0018",
    "\u0002\u00022<\u0005\b\u0005\u000534\u0007\u0006\u0002\u000245\u0007",
    "\u0018\u0002\u00025<\u0005\b\u0005\u000467\u0007\u0005\u0002\u00027",
    "8\u0005\u0006\u0004\u000289\u0007\u001d\u0002\u00029:\u0007\u001b\u0002",
    "\u0002:<\u0003\u0002\u0002\u0002;\u001e\u0003\u0002\u0002\u0002;!\u0003",
    "\u0002\u0002\u0002;#\u0003\u0002\u0002\u0002;$\u0003\u0002\u0002\u0002",
    ";%\u0003\u0002\u0002\u0002;&\u0003\u0002\u0002\u0002;\'\u0003\u0002",
    "\u0002\u0002;(\u0003\u0002\u0002\u0002;,\u0003\u0002\u0002\u0002;0\u0003",
    "\u0002\u0002\u0002;3\u0003\u0002\u0002\u0002;6\u0003\u0002\u0002\u0002",
    "<K\u0003\u0002\u0002\u0002=>\f\u0010\u0002\u0002>?\u0007\t\u0002\u0002",
    "?J\u0005\b\u0005\u0011@A\f\u000f\u0002\u0002AB\u0007\n\u0002\u0002B",
    "J\u0005\b\u0005\u0010CD\f\u000e\u0002\u0002DE\t\u0002\u0002\u0002EJ",
    "\u0005\b\u0005\u000fFG\f\r\u0002\u0002GH\t\u0003\u0002\u0002HJ\u0005",
    "\b\u0005\u000eI=\u0003\u0002\u0002\u0002I@\u0003\u0002\u0002\u0002I",
    "C\u0003\u0002\u0002\u0002IF\u0003\u0002\u0002\u0002JM\u0003\u0002\u0002",
    "\u0002KI\u0003\u0002\u0002\u0002KL\u0003\u0002\u0002\u0002L\t\u0003",
    "\u0002\u0002\u0002MK\u0003\u0002\u0002\u0002\b\u000e\u0017\u001a;IK"].join("");


var atn = new antlr4.atn.ATNDeserializer().deserialize(serializedATN);

var decisionsToDFA = atn.decisionToState.map( function(ds, index) { return new antlr4.dfa.DFA(ds, index); });

var sharedContextCache = new antlr4.PredictionContextCache();

var literalNames = [ null, "'assume'", "'forall'", "'define'", "'exists'", 
                     "'exit'", "'not'", "'and'", "'or'", "'implies'", "'=>'", 
                     "'->'", "'iff'", "'<=>'", "'<->'", "'true'", "'false'", 
                     "'('", "')'", "'['", "']'", null, null, null, null, 
                     null, "','", "':'" ];

var symbolicNames = [ null, "ASSUME", "FORALL", "DEFINE", "EXISTS", "EXIT", 
                      "NOT", "AND", "OR", "IMPLIES", "IMPLIES2", "IMPLIES3", 
                      "IFF", "IFF2", "IFF3", "TRUE", "FALSE", "BRACKET_OPEN", 
                      "BRACKET_CLOSE", "SQ_BRACKET_OPEN", "SQ_BRACKET_CLOSE", 
                      "LITERAL", "VARIABLE", "CONSTANT", "NAME", "TYPE", 
                      "COMMA", "COLON", "WS" ];

var ruleNames =  [ "statement", "parameter", "relation", "expression" ];

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
iProveParser.LITERAL = 21;
iProveParser.VARIABLE = 22;
iProveParser.CONSTANT = 23;
iProveParser.NAME = 24;
iProveParser.TYPE = 25;
iProveParser.COMMA = 26;
iProveParser.COLON = 27;
iProveParser.WS = 28;

iProveParser.RULE_statement = 0;
iProveParser.RULE_parameter = 1;
iProveParser.RULE_relation = 2;
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


function ParamConstContext(parser, ctx) {
	ParameterContext.call(this, parser);
    ParameterContext.prototype.copyFrom.call(this, ctx);
    return this;
}

ParamConstContext.prototype = Object.create(ParameterContext.prototype);
ParamConstContext.prototype.constructor = ParamConstContext;

iProveParser.ParamConstContext = ParamConstContext;

ParamConstContext.prototype.CONSTANT = function() {
    return this.getToken(iProveParser.CONSTANT, 0);
};
ParamConstContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterParamConst(this);
	}
};

ParamConstContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitParamConst(this);
	}
};

ParamConstContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitParamConst(this);
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
        case iProveParser.CONSTANT:
            localctx = new ParamConstContext(this, localctx);
            this.enterOuterAlt(localctx, 2);
            this.state = 11;
            this.match(iProveParser.CONSTANT);
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

function RelationContext(parser, parent, invokingState) {
	if(parent===undefined) {
	    parent = null;
	}
	if(invokingState===undefined || invokingState===null) {
		invokingState = -1;
	}
	antlr4.ParserRuleContext.call(this, parent, invokingState);
    this.parser = parser;
    this.ruleIndex = iProveParser.RULE_relation;
    return this;
}

RelationContext.prototype = Object.create(antlr4.ParserRuleContext.prototype);
RelationContext.prototype.constructor = RelationContext;

RelationContext.prototype.NAME = function() {
    return this.getToken(iProveParser.NAME, 0);
};

RelationContext.prototype.BRACKET_OPEN = function() {
    return this.getToken(iProveParser.BRACKET_OPEN, 0);
};

RelationContext.prototype.BRACKET_CLOSE = function() {
    return this.getToken(iProveParser.BRACKET_CLOSE, 0);
};

RelationContext.prototype.parameter = function(i) {
    if(i===undefined) {
        i = null;
    }
    if(i===null) {
        return this.getTypedRuleContexts(ParameterContext);
    } else {
        return this.getTypedRuleContext(ParameterContext,i);
    }
};

RelationContext.prototype.COMMA = function(i) {
	if(i===undefined) {
		i = null;
	}
    if(i===null) {
        return this.getTokens(iProveParser.COMMA);
    } else {
        return this.getToken(iProveParser.COMMA, i);
    }
};


RelationContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterRelation(this);
	}
};

RelationContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitRelation(this);
	}
};

RelationContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitRelation(this);
    } else {
        return visitor.visitChildren(this);
    }
};




iProveParser.RelationContext = RelationContext;

iProveParser.prototype.relation = function() {

    var localctx = new RelationContext(this, this._ctx, this.state);
    this.enterRule(localctx, 4, iProveParser.RULE_relation);
    var _la = 0; // Token type
    try {
        this.enterOuterAlt(localctx, 1);
        this.state = 14;
        this.match(iProveParser.NAME);
        this.state = 15;
        this.match(iProveParser.BRACKET_OPEN);
        this.state = 24;
        this._errHandler.sync(this);
        _la = this._input.LA(1);
        if(_la===iProveParser.VARIABLE || _la===iProveParser.CONSTANT) {
            this.state = 16;
            this.parameter();
            this.state = 21;
            this._errHandler.sync(this);
            _la = this._input.LA(1);
            while(_la===iProveParser.COMMA) {
                this.state = 17;
                this.match(iProveParser.COMMA);
                this.state = 18;
                this.parameter();
                this.state = 23;
                this._errHandler.sync(this);
                _la = this._input.LA(1);
            }
        }

        this.state = 26;
        this.match(iProveParser.BRACKET_CLOSE);
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


function RelationExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

RelationExpContext.prototype = Object.create(ExpressionContext.prototype);
RelationExpContext.prototype.constructor = RelationExpContext;

iProveParser.RelationExpContext = RelationExpContext;

RelationExpContext.prototype.relation = function() {
    return this.getTypedRuleContext(RelationContext,0);
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

ExistsExpContext.prototype.VARIABLE = function() {
    return this.getToken(iProveParser.VARIABLE, 0);
};

ExistsExpContext.prototype.expression = function() {
    return this.getTypedRuleContext(ExpressionContext,0);
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


function LiteralExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

LiteralExpContext.prototype = Object.create(ExpressionContext.prototype);
LiteralExpContext.prototype.constructor = LiteralExpContext;

iProveParser.LiteralExpContext = LiteralExpContext;

LiteralExpContext.prototype.LITERAL = function() {
    return this.getToken(iProveParser.LITERAL, 0);
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

ForallExpContext.prototype.VARIABLE = function() {
    return this.getToken(iProveParser.VARIABLE, 0);
};

ForallExpContext.prototype.expression = function() {
    return this.getTypedRuleContext(ExpressionContext,0);
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


function FuncDefinitionContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

FuncDefinitionContext.prototype = Object.create(ExpressionContext.prototype);
FuncDefinitionContext.prototype.constructor = FuncDefinitionContext;

iProveParser.FuncDefinitionContext = FuncDefinitionContext;

FuncDefinitionContext.prototype.DEFINE = function() {
    return this.getToken(iProveParser.DEFINE, 0);
};

FuncDefinitionContext.prototype.relation = function() {
    return this.getTypedRuleContext(RelationContext,0);
};

FuncDefinitionContext.prototype.COLON = function() {
    return this.getToken(iProveParser.COLON, 0);
};

FuncDefinitionContext.prototype.TYPE = function() {
    return this.getToken(iProveParser.TYPE, 0);
};
FuncDefinitionContext.prototype.enterRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.enterFuncDefinition(this);
	}
};

FuncDefinitionContext.prototype.exitRule = function(listener) {
    if(listener instanceof iProveListener ) {
        listener.exitFuncDefinition(this);
	}
};

FuncDefinitionContext.prototype.accept = function(visitor) {
    if ( visitor instanceof iProveVisitor ) {
        return visitor.visitFuncDefinition(this);
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
        this.state = 57;
        this._errHandler.sync(this);
        switch(this._input.LA(1)) {
        case iProveParser.NOT:
            localctx = new NotExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;

            this.state = 29;
            this.match(iProveParser.NOT);
            this.state = 30;
            this.expression(16);
            break;
        case iProveParser.ASSUME:
            localctx = new AssumeExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 31;
            this.match(iProveParser.ASSUME);
            this.state = 32;
            this.expression(15);
            break;
        case iProveParser.LITERAL:
            localctx = new LiteralExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 33;
            this.match(iProveParser.LITERAL);
            break;
        case iProveParser.TRUE:
            localctx = new TrueExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 34;
            this.match(iProveParser.TRUE);
            break;
        case iProveParser.FALSE:
            localctx = new FalseExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 35;
            this.match(iProveParser.FALSE);
            break;
        case iProveParser.EXIT:
            localctx = new ExitExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 36;
            this.match(iProveParser.EXIT);
            break;
        case iProveParser.NAME:
            localctx = new RelationExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 37;
            this.relation();
            break;
        case iProveParser.BRACKET_OPEN:
            localctx = new ParenthesesExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 38;
            this.match(iProveParser.BRACKET_OPEN);
            this.state = 39;
            this.expression(0);
            this.state = 40;
            this.match(iProveParser.BRACKET_CLOSE);
            break;
        case iProveParser.SQ_BRACKET_OPEN:
            localctx = new SqParenthesesExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 42;
            this.match(iProveParser.SQ_BRACKET_OPEN);
            this.state = 43;
            this.expression(0);
            this.state = 44;
            this.match(iProveParser.SQ_BRACKET_CLOSE);
            break;
        case iProveParser.FORALL:
            localctx = new ForallExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 46;
            this.match(iProveParser.FORALL);
            this.state = 47;
            this.match(iProveParser.VARIABLE);
            this.state = 48;
            this.expression(3);
            break;
        case iProveParser.EXISTS:
            localctx = new ExistsExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 49;
            this.match(iProveParser.EXISTS);
            this.state = 50;
            this.match(iProveParser.VARIABLE);
            this.state = 51;
            this.expression(2);
            break;
        case iProveParser.DEFINE:
            localctx = new FuncDefinitionContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 52;
            this.match(iProveParser.DEFINE);
            this.state = 53;
            this.relation();
            this.state = 54;
            this.match(iProveParser.COLON);
            this.state = 55;
            this.match(iProveParser.TYPE);
            break;
        default:
            throw new antlr4.error.NoViableAltException(this);
        }
        this._ctx.stop = this._input.LT(-1);
        this.state = 73;
        this._errHandler.sync(this);
        var _alt = this._interp.adaptivePredict(this._input,5,this._ctx)
        while(_alt!=2 && _alt!=antlr4.atn.ATN.INVALID_ALT_NUMBER) {
            if(_alt===1) {
                if(this._parseListeners!==null) {
                    this.triggerExitRuleEvent();
                }
                _prevctx = localctx;
                this.state = 71;
                this._errHandler.sync(this);
                var la_ = this._interp.adaptivePredict(this._input,4,this._ctx);
                switch(la_) {
                case 1:
                    localctx = new AndExpContext(this, new ExpressionContext(this, _parentctx, _parentState));
                    this.pushNewRecursionContext(localctx, _startState, iProveParser.RULE_expression);
                    this.state = 59;
                    if (!( this.precpred(this._ctx, 14))) {
                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 14)");
                    }
                    this.state = 60;
                    this.match(iProveParser.AND);
                    this.state = 61;
                    this.expression(15);
                    break;

                case 2:
                    localctx = new OrExpContext(this, new ExpressionContext(this, _parentctx, _parentState));
                    this.pushNewRecursionContext(localctx, _startState, iProveParser.RULE_expression);
                    this.state = 62;
                    if (!( this.precpred(this._ctx, 13))) {
                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 13)");
                    }
                    this.state = 63;
                    this.match(iProveParser.OR);
                    this.state = 64;
                    this.expression(14);
                    break;

                case 3:
                    localctx = new ImpliesExpContext(this, new ExpressionContext(this, _parentctx, _parentState));
                    this.pushNewRecursionContext(localctx, _startState, iProveParser.RULE_expression);
                    this.state = 65;
                    if (!( this.precpred(this._ctx, 12))) {
                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 12)");
                    }
                    this.state = 66;
                    _la = this._input.LA(1);
                    if(!((((_la) & ~0x1f) == 0 && ((1 << _la) & ((1 << iProveParser.IMPLIES) | (1 << iProveParser.IMPLIES2) | (1 << iProveParser.IMPLIES3))) !== 0))) {
                    this._errHandler.recoverInline(this);
                    }
                    else {
                    	this._errHandler.reportMatch(this);
                        this.consume();
                    }
                    this.state = 67;
                    this.expression(13);
                    break;

                case 4:
                    localctx = new IffExpContext(this, new ExpressionContext(this, _parentctx, _parentState));
                    this.pushNewRecursionContext(localctx, _startState, iProveParser.RULE_expression);
                    this.state = 68;
                    if (!( this.precpred(this._ctx, 11))) {
                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 11)");
                    }
                    this.state = 69;
                    _la = this._input.LA(1);
                    if(!((((_la) & ~0x1f) == 0 && ((1 << _la) & ((1 << iProveParser.IFF) | (1 << iProveParser.IFF2) | (1 << iProveParser.IFF3))) !== 0))) {
                    this._errHandler.recoverInline(this);
                    }
                    else {
                    	this._errHandler.reportMatch(this);
                        this.consume();
                    }
                    this.state = 70;
                    this.expression(12);
                    break;

                } 
            }
            this.state = 75;
            this._errHandler.sync(this);
            _alt = this._interp.adaptivePredict(this._input,5,this._ctx);
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
			return this.precpred(this._ctx, 14);
		case 1:
			return this.precpred(this._ctx, 13);
		case 2:
			return this.precpred(this._ctx, 12);
		case 3:
			return this.precpred(this._ctx, 11);
		default:
			throw "No predicate with index:" + predIndex;
	}
};


exports.iProveParser = iProveParser;
