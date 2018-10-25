// Generated from src/parser/Propositional.g4 by ANTLR 4.7.1
// jshint ignore: start
var antlr4 = require('antlr4/index');
var PropositionalListener = require('./PropositionalListener').PropositionalListener;
var PropositionalVisitor = require('./PropositionalVisitor').PropositionalVisitor;

var grammarFileName = "Propositional.g4";

var serializedATN = ["\u0003\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964",
    "\u0003\u0013D\u0004\u0002\t\u0002\u0004\u0003\t\u0003\u0004\u0004\t",
    "\u0004\u0003\u0002\u0003\u0002\u0003\u0003\u0003\u0003\u0003\u0003\u0003",
    "\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003",
    "\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003",
    "\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003",
    "\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0007",
    "\u0003&\n\u0003\f\u0003\u000e\u0003)\u000b\u0003\u0003\u0003\u0003\u0003",
    "\u0005\u0003-\n\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003",
    "\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003",
    "\u0003\u0003\u0003\u0003\u0007\u0003;\n\u0003\f\u0003\u000e\u0003>\u000b",
    "\u0003\u0003\u0004\u0003\u0004\u0005\u0004B\n\u0004\u0003\u0004\u0002",
    "\u0003\u0004\u0005\u0002\u0004\u0006\u0002\u0002\u0002M\u0002\b\u0003",
    "\u0002\u0002\u0002\u0004,\u0003\u0002\u0002\u0002\u0006A\u0003\u0002",
    "\u0002\u0002\b\t\u0005\u0004\u0003\u0002\t\u0003\u0003\u0002\u0002\u0002",
    "\n\u000b\b\u0003\u0001\u0002\u000b\f\u0007\u0004\u0002\u0002\f-\u0005",
    "\u0004\u0003\u000e\r-\u0007\u0003\u0002\u0002\u000e-\u0007\t\u0002\u0002",
    "\u000f-\u0007\n\u0002\u0002\u0010\u0011\u0007\u000b\u0002\u0002\u0011",
    "\u0012\u0005\u0004\u0003\u0002\u0012\u0013\u0007\f\u0002\u0002\u0013",
    "-\u0003\u0002\u0002\u0002\u0014\u0015\u0007\u0010\u0002\u0002\u0015",
    "\u0016\u0007\r\u0002\u0002\u0016\u0017\u0007\u000b\u0002\u0002\u0017",
    "\u0018\u0005\u0004\u0003\u0002\u0018\u0019\u0007\f\u0002\u0002\u0019",
    "-\u0003\u0002\u0002\u0002\u001a\u001b\u0007\u0011\u0002\u0002\u001b",
    "\u001c\u0007\r\u0002\u0002\u001c\u001d\u0007\u000b\u0002\u0002\u001d",
    "\u001e\u0005\u0004\u0003\u0002\u001e\u001f\u0007\f\u0002\u0002\u001f",
    "-\u0003\u0002\u0002\u0002 !\u0007\u000f\u0002\u0002!\"\u0007\u000b\u0002",
    "\u0002\"\'\u0005\u0006\u0004\u0002#$\u0007\u0012\u0002\u0002$&\u0005",
    "\u0006\u0004\u0002%#\u0003\u0002\u0002\u0002&)\u0003\u0002\u0002\u0002",
    "\'%\u0003\u0002\u0002\u0002\'(\u0003\u0002\u0002\u0002(*\u0003\u0002",
    "\u0002\u0002)\'\u0003\u0002\u0002\u0002*+\u0007\f\u0002\u0002+-\u0003",
    "\u0002\u0002\u0002,\n\u0003\u0002\u0002\u0002,\r\u0003\u0002\u0002\u0002",
    ",\u000e\u0003\u0002\u0002\u0002,\u000f\u0003\u0002\u0002\u0002,\u0010",
    "\u0003\u0002\u0002\u0002,\u0014\u0003\u0002\u0002\u0002,\u001a\u0003",
    "\u0002\u0002\u0002, \u0003\u0002\u0002\u0002-<\u0003\u0002\u0002\u0002",
    "./\f\r\u0002\u0002/0\u0007\u0005\u0002\u00020;\u0005\u0004\u0003\u000e",
    "12\f\f\u0002\u000223\u0007\u0006\u0002\u00023;\u0005\u0004\u0003\r4",
    "5\f\u000b\u0002\u000256\u0007\u0007\u0002\u00026;\u0005\u0004\u0003",
    "\f78\f\n\u0002\u000289\u0007\b\u0002\u00029;\u0005\u0004\u0003\u000b",
    ":.\u0003\u0002\u0002\u0002:1\u0003\u0002\u0002\u0002:4\u0003\u0002\u0002",
    "\u0002:7\u0003\u0002\u0002\u0002;>\u0003\u0002\u0002\u0002<:\u0003\u0002",
    "\u0002\u0002<=\u0003\u0002\u0002\u0002=\u0005\u0003\u0002\u0002\u0002",
    "><\u0003\u0002\u0002\u0002?B\u0007\r\u0002\u0002@B\u0007\u000e\u0002",
    "\u0002A?\u0003\u0002\u0002\u0002A@\u0003\u0002\u0002\u0002B\u0007\u0003",
    "\u0002\u0002\u0002\u0007\',:<A"].join("");


var atn = new antlr4.atn.ATNDeserializer().deserialize(serializedATN);

var decisionsToDFA = atn.decisionToState.map( function(ds, index) { return new antlr4.dfa.DFA(ds, index); });

var sharedContextCache = new antlr4.PredictionContextCache();

var literalNames = [ null, null, "'not'", "'and'", "'or'", "'implies'", 
                     "'iff'", "'true'", "'false'", "'('", "')'", null, null, 
                     null, "'forall'", "'exists'", "','" ];

var symbolicNames = [ null, "LITERAL", "NOT", "AND", "OR", "IMPLIES", "IFF", 
                      "TRUE", "FALSE", "BRACKET_OPEN", "BRACKET_CLOSE", 
                      "VARIABLE", "CONSTANT", "NAME", "FORALL", "EXISTS", 
                      "COMMA", "WS" ];

var ruleNames =  [ "statement", "expression", "parameter" ];

function PropositionalParser (input) {
	antlr4.Parser.call(this, input);
    this._interp = new antlr4.atn.ParserATNSimulator(this, atn, decisionsToDFA, sharedContextCache);
    this.ruleNames = ruleNames;
    this.literalNames = literalNames;
    this.symbolicNames = symbolicNames;
    return this;
}

PropositionalParser.prototype = Object.create(antlr4.Parser.prototype);
PropositionalParser.prototype.constructor = PropositionalParser;

Object.defineProperty(PropositionalParser.prototype, "atn", {
	get : function() {
		return atn;
	}
});

PropositionalParser.EOF = antlr4.Token.EOF;
PropositionalParser.LITERAL = 1;
PropositionalParser.NOT = 2;
PropositionalParser.AND = 3;
PropositionalParser.OR = 4;
PropositionalParser.IMPLIES = 5;
PropositionalParser.IFF = 6;
PropositionalParser.TRUE = 7;
PropositionalParser.FALSE = 8;
PropositionalParser.BRACKET_OPEN = 9;
PropositionalParser.BRACKET_CLOSE = 10;
PropositionalParser.VARIABLE = 11;
PropositionalParser.CONSTANT = 12;
PropositionalParser.NAME = 13;
PropositionalParser.FORALL = 14;
PropositionalParser.EXISTS = 15;
PropositionalParser.COMMA = 16;
PropositionalParser.WS = 17;

PropositionalParser.RULE_statement = 0;
PropositionalParser.RULE_expression = 1;
PropositionalParser.RULE_parameter = 2;

function StatementContext(parser, parent, invokingState) {
	if(parent===undefined) {
	    parent = null;
	}
	if(invokingState===undefined || invokingState===null) {
		invokingState = -1;
	}
	antlr4.ParserRuleContext.call(this, parent, invokingState);
    this.parser = parser;
    this.ruleIndex = PropositionalParser.RULE_statement;
    return this;
}

StatementContext.prototype = Object.create(antlr4.ParserRuleContext.prototype);
StatementContext.prototype.constructor = StatementContext;

StatementContext.prototype.expression = function() {
    return this.getTypedRuleContext(ExpressionContext,0);
};

StatementContext.prototype.enterRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.enterStatement(this);
	}
};

StatementContext.prototype.exitRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.exitStatement(this);
	}
};

StatementContext.prototype.accept = function(visitor) {
    if ( visitor instanceof PropositionalVisitor ) {
        return visitor.visitStatement(this);
    } else {
        return visitor.visitChildren(this);
    }
};




PropositionalParser.StatementContext = StatementContext;

PropositionalParser.prototype.statement = function() {

    var localctx = new StatementContext(this, this._ctx, this.state);
    this.enterRule(localctx, 0, PropositionalParser.RULE_statement);
    try {
        this.enterOuterAlt(localctx, 1);
        this.state = 6;
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

function ExpressionContext(parser, parent, invokingState) {
	if(parent===undefined) {
	    parent = null;
	}
	if(invokingState===undefined || invokingState===null) {
		invokingState = -1;
	}
	antlr4.ParserRuleContext.call(this, parent, invokingState);
    this.parser = parser;
    this.ruleIndex = PropositionalParser.RULE_expression;
    return this;
}

ExpressionContext.prototype = Object.create(antlr4.ParserRuleContext.prototype);
ExpressionContext.prototype.constructor = ExpressionContext;


 
ExpressionContext.prototype.copyFrom = function(ctx) {
    antlr4.ParserRuleContext.prototype.copyFrom.call(this, ctx);
};

function ExistsExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

ExistsExpContext.prototype = Object.create(ExpressionContext.prototype);
ExistsExpContext.prototype.constructor = ExistsExpContext;

PropositionalParser.ExistsExpContext = ExistsExpContext;

ExistsExpContext.prototype.EXISTS = function() {
    return this.getToken(PropositionalParser.EXISTS, 0);
};

ExistsExpContext.prototype.VARIABLE = function() {
    return this.getToken(PropositionalParser.VARIABLE, 0);
};

ExistsExpContext.prototype.BRACKET_OPEN = function() {
    return this.getToken(PropositionalParser.BRACKET_OPEN, 0);
};

ExistsExpContext.prototype.expression = function() {
    return this.getTypedRuleContext(ExpressionContext,0);
};

ExistsExpContext.prototype.BRACKET_CLOSE = function() {
    return this.getToken(PropositionalParser.BRACKET_CLOSE, 0);
};
ExistsExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.enterExistsExp(this);
	}
};

ExistsExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.exitExistsExp(this);
	}
};

ExistsExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof PropositionalVisitor ) {
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

PropositionalParser.LiteralExpContext = LiteralExpContext;

LiteralExpContext.prototype.LITERAL = function() {
    return this.getToken(PropositionalParser.LITERAL, 0);
};
LiteralExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.enterLiteralExp(this);
	}
};

LiteralExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.exitLiteralExp(this);
	}
};

LiteralExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof PropositionalVisitor ) {
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

PropositionalParser.ForallExpContext = ForallExpContext;

ForallExpContext.prototype.FORALL = function() {
    return this.getToken(PropositionalParser.FORALL, 0);
};

ForallExpContext.prototype.VARIABLE = function() {
    return this.getToken(PropositionalParser.VARIABLE, 0);
};

ForallExpContext.prototype.BRACKET_OPEN = function() {
    return this.getToken(PropositionalParser.BRACKET_OPEN, 0);
};

ForallExpContext.prototype.expression = function() {
    return this.getTypedRuleContext(ExpressionContext,0);
};

ForallExpContext.prototype.BRACKET_CLOSE = function() {
    return this.getToken(PropositionalParser.BRACKET_CLOSE, 0);
};
ForallExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.enterForallExp(this);
	}
};

ForallExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.exitForallExp(this);
	}
};

ForallExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof PropositionalVisitor ) {
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

PropositionalParser.TrueExpContext = TrueExpContext;

TrueExpContext.prototype.TRUE = function() {
    return this.getToken(PropositionalParser.TRUE, 0);
};
TrueExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.enterTrueExp(this);
	}
};

TrueExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.exitTrueExp(this);
	}
};

TrueExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof PropositionalVisitor ) {
        return visitor.visitTrueExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function AndExpContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

AndExpContext.prototype = Object.create(ExpressionContext.prototype);
AndExpContext.prototype.constructor = AndExpContext;

PropositionalParser.AndExpContext = AndExpContext;

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
    return this.getToken(PropositionalParser.AND, 0);
};
AndExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.enterAndExp(this);
	}
};

AndExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.exitAndExp(this);
	}
};

AndExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof PropositionalVisitor ) {
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

PropositionalParser.ParenthesesExpContext = ParenthesesExpContext;

ParenthesesExpContext.prototype.BRACKET_OPEN = function() {
    return this.getToken(PropositionalParser.BRACKET_OPEN, 0);
};

ParenthesesExpContext.prototype.expression = function() {
    return this.getTypedRuleContext(ExpressionContext,0);
};

ParenthesesExpContext.prototype.BRACKET_CLOSE = function() {
    return this.getToken(PropositionalParser.BRACKET_CLOSE, 0);
};
ParenthesesExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.enterParenthesesExp(this);
	}
};

ParenthesesExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.exitParenthesesExp(this);
	}
};

ParenthesesExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof PropositionalVisitor ) {
        return visitor.visitParenthesesExp(this);
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

PropositionalParser.FalseExpContext = FalseExpContext;

FalseExpContext.prototype.FALSE = function() {
    return this.getToken(PropositionalParser.FALSE, 0);
};
FalseExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.enterFalseExp(this);
	}
};

FalseExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.exitFalseExp(this);
	}
};

FalseExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof PropositionalVisitor ) {
        return visitor.visitFalseExp(this);
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

PropositionalParser.OrExpContext = OrExpContext;

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
    return this.getToken(PropositionalParser.OR, 0);
};
OrExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.enterOrExp(this);
	}
};

OrExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.exitOrExp(this);
	}
};

OrExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof PropositionalVisitor ) {
        return visitor.visitOrExp(this);
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

PropositionalParser.NotExpContext = NotExpContext;

NotExpContext.prototype.NOT = function() {
    return this.getToken(PropositionalParser.NOT, 0);
};

NotExpContext.prototype.expression = function() {
    return this.getTypedRuleContext(ExpressionContext,0);
};
NotExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.enterNotExp(this);
	}
};

NotExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.exitNotExp(this);
	}
};

NotExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof PropositionalVisitor ) {
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

PropositionalParser.IffExpContext = IffExpContext;

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
    return this.getToken(PropositionalParser.IFF, 0);
};
IffExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.enterIffExp(this);
	}
};

IffExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.exitIffExp(this);
	}
};

IffExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof PropositionalVisitor ) {
        return visitor.visitIffExp(this);
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

PropositionalParser.ImpliesExpContext = ImpliesExpContext;

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
    return this.getToken(PropositionalParser.IMPLIES, 0);
};
ImpliesExpContext.prototype.enterRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.enterImpliesExp(this);
	}
};

ImpliesExpContext.prototype.exitRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.exitImpliesExp(this);
	}
};

ImpliesExpContext.prototype.accept = function(visitor) {
    if ( visitor instanceof PropositionalVisitor ) {
        return visitor.visitImpliesExp(this);
    } else {
        return visitor.visitChildren(this);
    }
};


function RelationContext(parser, ctx) {
	ExpressionContext.call(this, parser);
    ExpressionContext.prototype.copyFrom.call(this, ctx);
    return this;
}

RelationContext.prototype = Object.create(ExpressionContext.prototype);
RelationContext.prototype.constructor = RelationContext;

PropositionalParser.RelationContext = RelationContext;

RelationContext.prototype.NAME = function() {
    return this.getToken(PropositionalParser.NAME, 0);
};

RelationContext.prototype.BRACKET_OPEN = function() {
    return this.getToken(PropositionalParser.BRACKET_OPEN, 0);
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

RelationContext.prototype.BRACKET_CLOSE = function() {
    return this.getToken(PropositionalParser.BRACKET_CLOSE, 0);
};

RelationContext.prototype.COMMA = function(i) {
	if(i===undefined) {
		i = null;
	}
    if(i===null) {
        return this.getTokens(PropositionalParser.COMMA);
    } else {
        return this.getToken(PropositionalParser.COMMA, i);
    }
};

RelationContext.prototype.enterRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.enterRelation(this);
	}
};

RelationContext.prototype.exitRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.exitRelation(this);
	}
};

RelationContext.prototype.accept = function(visitor) {
    if ( visitor instanceof PropositionalVisitor ) {
        return visitor.visitRelation(this);
    } else {
        return visitor.visitChildren(this);
    }
};



PropositionalParser.prototype.expression = function(_p) {
	if(_p===undefined) {
	    _p = 0;
	}
    var _parentctx = this._ctx;
    var _parentState = this.state;
    var localctx = new ExpressionContext(this, this._ctx, _parentState);
    var _prevctx = localctx;
    var _startState = 2;
    this.enterRecursionRule(localctx, 2, PropositionalParser.RULE_expression, _p);
    var _la = 0; // Token type
    try {
        this.enterOuterAlt(localctx, 1);
        this.state = 42;
        this._errHandler.sync(this);
        switch(this._input.LA(1)) {
        case PropositionalParser.NOT:
            localctx = new NotExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;

            this.state = 9;
            this.match(PropositionalParser.NOT);
            this.state = 10;
            this.expression(12);
            break;
        case PropositionalParser.LITERAL:
            localctx = new LiteralExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 11;
            this.match(PropositionalParser.LITERAL);
            break;
        case PropositionalParser.TRUE:
            localctx = new TrueExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 12;
            this.match(PropositionalParser.TRUE);
            break;
        case PropositionalParser.FALSE:
            localctx = new FalseExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 13;
            this.match(PropositionalParser.FALSE);
            break;
        case PropositionalParser.BRACKET_OPEN:
            localctx = new ParenthesesExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 14;
            this.match(PropositionalParser.BRACKET_OPEN);
            this.state = 15;
            this.expression(0);
            this.state = 16;
            this.match(PropositionalParser.BRACKET_CLOSE);
            break;
        case PropositionalParser.FORALL:
            localctx = new ForallExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 18;
            this.match(PropositionalParser.FORALL);
            this.state = 19;
            this.match(PropositionalParser.VARIABLE);
            this.state = 20;
            this.match(PropositionalParser.BRACKET_OPEN);
            this.state = 21;
            this.expression(0);
            this.state = 22;
            this.match(PropositionalParser.BRACKET_CLOSE);
            break;
        case PropositionalParser.EXISTS:
            localctx = new ExistsExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 24;
            this.match(PropositionalParser.EXISTS);
            this.state = 25;
            this.match(PropositionalParser.VARIABLE);
            this.state = 26;
            this.match(PropositionalParser.BRACKET_OPEN);
            this.state = 27;
            this.expression(0);
            this.state = 28;
            this.match(PropositionalParser.BRACKET_CLOSE);
            break;
        case PropositionalParser.NAME:
            localctx = new RelationContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 30;
            this.match(PropositionalParser.NAME);
            this.state = 31;
            this.match(PropositionalParser.BRACKET_OPEN);
            this.state = 32;
            this.parameter();
            this.state = 37;
            this._errHandler.sync(this);
            _la = this._input.LA(1);
            while(_la===PropositionalParser.COMMA) {
                this.state = 33;
                this.match(PropositionalParser.COMMA);
                this.state = 34;
                this.parameter();
                this.state = 39;
                this._errHandler.sync(this);
                _la = this._input.LA(1);
            }
            this.state = 40;
            this.match(PropositionalParser.BRACKET_CLOSE);
            break;
        default:
            throw new antlr4.error.NoViableAltException(this);
        }
        this._ctx.stop = this._input.LT(-1);
        this.state = 58;
        this._errHandler.sync(this);
        var _alt = this._interp.adaptivePredict(this._input,3,this._ctx)
        while(_alt!=2 && _alt!=antlr4.atn.ATN.INVALID_ALT_NUMBER) {
            if(_alt===1) {
                if(this._parseListeners!==null) {
                    this.triggerExitRuleEvent();
                }
                _prevctx = localctx;
                this.state = 56;
                this._errHandler.sync(this);
                var la_ = this._interp.adaptivePredict(this._input,2,this._ctx);
                switch(la_) {
                case 1:
                    localctx = new AndExpContext(this, new ExpressionContext(this, _parentctx, _parentState));
                    this.pushNewRecursionContext(localctx, _startState, PropositionalParser.RULE_expression);
                    this.state = 44;
                    if (!( this.precpred(this._ctx, 11))) {
                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 11)");
                    }
                    this.state = 45;
                    this.match(PropositionalParser.AND);
                    this.state = 46;
                    this.expression(12);
                    break;

                case 2:
                    localctx = new OrExpContext(this, new ExpressionContext(this, _parentctx, _parentState));
                    this.pushNewRecursionContext(localctx, _startState, PropositionalParser.RULE_expression);
                    this.state = 47;
                    if (!( this.precpred(this._ctx, 10))) {
                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 10)");
                    }
                    this.state = 48;
                    this.match(PropositionalParser.OR);
                    this.state = 49;
                    this.expression(11);
                    break;

                case 3:
                    localctx = new ImpliesExpContext(this, new ExpressionContext(this, _parentctx, _parentState));
                    this.pushNewRecursionContext(localctx, _startState, PropositionalParser.RULE_expression);
                    this.state = 50;
                    if (!( this.precpred(this._ctx, 9))) {
                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 9)");
                    }
                    this.state = 51;
                    this.match(PropositionalParser.IMPLIES);
                    this.state = 52;
                    this.expression(10);
                    break;

                case 4:
                    localctx = new IffExpContext(this, new ExpressionContext(this, _parentctx, _parentState));
                    this.pushNewRecursionContext(localctx, _startState, PropositionalParser.RULE_expression);
                    this.state = 53;
                    if (!( this.precpred(this._ctx, 8))) {
                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 8)");
                    }
                    this.state = 54;
                    this.match(PropositionalParser.IFF);
                    this.state = 55;
                    this.expression(9);
                    break;

                } 
            }
            this.state = 60;
            this._errHandler.sync(this);
            _alt = this._interp.adaptivePredict(this._input,3,this._ctx);
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

function ParameterContext(parser, parent, invokingState) {
	if(parent===undefined) {
	    parent = null;
	}
	if(invokingState===undefined || invokingState===null) {
		invokingState = -1;
	}
	antlr4.ParserRuleContext.call(this, parent, invokingState);
    this.parser = parser;
    this.ruleIndex = PropositionalParser.RULE_parameter;
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

PropositionalParser.ParamConstContext = ParamConstContext;

ParamConstContext.prototype.CONSTANT = function() {
    return this.getToken(PropositionalParser.CONSTANT, 0);
};
ParamConstContext.prototype.enterRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.enterParamConst(this);
	}
};

ParamConstContext.prototype.exitRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.exitParamConst(this);
	}
};

ParamConstContext.prototype.accept = function(visitor) {
    if ( visitor instanceof PropositionalVisitor ) {
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

PropositionalParser.ParamVarContext = ParamVarContext;

ParamVarContext.prototype.VARIABLE = function() {
    return this.getToken(PropositionalParser.VARIABLE, 0);
};
ParamVarContext.prototype.enterRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.enterParamVar(this);
	}
};

ParamVarContext.prototype.exitRule = function(listener) {
    if(listener instanceof PropositionalListener ) {
        listener.exitParamVar(this);
	}
};

ParamVarContext.prototype.accept = function(visitor) {
    if ( visitor instanceof PropositionalVisitor ) {
        return visitor.visitParamVar(this);
    } else {
        return visitor.visitChildren(this);
    }
};



PropositionalParser.ParameterContext = ParameterContext;

PropositionalParser.prototype.parameter = function() {

    var localctx = new ParameterContext(this, this._ctx, this.state);
    this.enterRule(localctx, 4, PropositionalParser.RULE_parameter);
    try {
        this.state = 63;
        this._errHandler.sync(this);
        switch(this._input.LA(1)) {
        case PropositionalParser.VARIABLE:
            localctx = new ParamVarContext(this, localctx);
            this.enterOuterAlt(localctx, 1);
            this.state = 61;
            this.match(PropositionalParser.VARIABLE);
            break;
        case PropositionalParser.CONSTANT:
            localctx = new ParamConstContext(this, localctx);
            this.enterOuterAlt(localctx, 2);
            this.state = 62;
            this.match(PropositionalParser.CONSTANT);
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


PropositionalParser.prototype.sempred = function(localctx, ruleIndex, predIndex) {
	switch(ruleIndex) {
	case 1:
			return this.expression_sempred(localctx, predIndex);
    default:
        throw "No predicate with index:" + ruleIndex;
   }
};

PropositionalParser.prototype.expression_sempred = function(localctx, predIndex) {
	switch(predIndex) {
		case 0:
			return this.precpred(this._ctx, 11);
		case 1:
			return this.precpred(this._ctx, 10);
		case 2:
			return this.precpred(this._ctx, 9);
		case 3:
			return this.precpred(this._ctx, 8);
		default:
			throw "No predicate with index:" + predIndex;
	}
};


exports.PropositionalParser = PropositionalParser;
