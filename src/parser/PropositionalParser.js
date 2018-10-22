// Generated from src/parser/Propositional.g4 by ANTLR 4.7.1
// jshint ignore: start
var antlr4 = require('antlr4/index');
var PropositionalListener = require('./PropositionalListener').PropositionalListener;
var PropositionalVisitor = require('./PropositionalVisitor').PropositionalVisitor;

var grammarFileName = "Propositional.g4";

var serializedATN = ["\u0003\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964",
    "\u0003\r&\u0004\u0002\t\u0002\u0004\u0003\t\u0003\u0003\u0002\u0003",
    "\u0002\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003",
    "\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0005\u0003\u0013",
    "\n\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003",
    "\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003",
    "\u0003\u0003\u0007\u0003!\n\u0003\f\u0003\u000e\u0003$\u000b\u0003\u0003",
    "\u0003\u0002\u0003\u0004\u0004\u0002\u0004\u0002\u0002\u0002+\u0002",
    "\u0006\u0003\u0002\u0002\u0002\u0004\u0012\u0003\u0002\u0002\u0002\u0006",
    "\u0007\u0005\u0004\u0003\u0002\u0007\u0003\u0003\u0002\u0002\u0002\b",
    "\t\b\u0003\u0001\u0002\t\n\u0007\u0004\u0002\u0002\n\u0013\u0005\u0004",
    "\u0003\u000b\u000b\u0013\u0007\u0003\u0002\u0002\f\u0013\u0007\t\u0002",
    "\u0002\r\u0013\u0007\n\u0002\u0002\u000e\u000f\u0007\u000b\u0002\u0002",
    "\u000f\u0010\u0005\u0004\u0003\u0002\u0010\u0011\u0007\f\u0002\u0002",
    "\u0011\u0013\u0003\u0002\u0002\u0002\u0012\b\u0003\u0002\u0002\u0002",
    "\u0012\u000b\u0003\u0002\u0002\u0002\u0012\f\u0003\u0002\u0002\u0002",
    "\u0012\r\u0003\u0002\u0002\u0002\u0012\u000e\u0003\u0002\u0002\u0002",
    "\u0013\"\u0003\u0002\u0002\u0002\u0014\u0015\f\n\u0002\u0002\u0015\u0016",
    "\u0007\u0005\u0002\u0002\u0016!\u0005\u0004\u0003\u000b\u0017\u0018",
    "\f\t\u0002\u0002\u0018\u0019\u0007\u0006\u0002\u0002\u0019!\u0005\u0004",
    "\u0003\n\u001a\u001b\f\b\u0002\u0002\u001b\u001c\u0007\u0007\u0002\u0002",
    "\u001c!\u0005\u0004\u0003\t\u001d\u001e\f\u0007\u0002\u0002\u001e\u001f",
    "\u0007\b\u0002\u0002\u001f!\u0005\u0004\u0003\b \u0014\u0003\u0002\u0002",
    "\u0002 \u0017\u0003\u0002\u0002\u0002 \u001a\u0003\u0002\u0002\u0002",
    " \u001d\u0003\u0002\u0002\u0002!$\u0003\u0002\u0002\u0002\" \u0003\u0002",
    "\u0002\u0002\"#\u0003\u0002\u0002\u0002#\u0005\u0003\u0002\u0002\u0002",
    "$\"\u0003\u0002\u0002\u0002\u0005\u0012 \""].join("");


var atn = new antlr4.atn.ATNDeserializer().deserialize(serializedATN);

var decisionsToDFA = atn.decisionToState.map( function(ds, index) { return new antlr4.dfa.DFA(ds, index); });

var sharedContextCache = new antlr4.PredictionContextCache();

var literalNames = [ null, null, "'not'", "'and'", "'or'", "'implies'", 
                     "'iff'", "'true'", "'false'", "'('", "')'" ];

var symbolicNames = [ null, "LITERAL", "NOT", "AND", "OR", "IMPLIES", "IFF", 
                      "TRUE", "FALSE", "BRACKET_OPEN", "BRACKET_CLOSE", 
                      "WS" ];

var ruleNames =  [ "statement", "expression" ];

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
PropositionalParser.WS = 11;

PropositionalParser.RULE_statement = 0;
PropositionalParser.RULE_expression = 1;

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
        this.state = 4;
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
    try {
        this.enterOuterAlt(localctx, 1);
        this.state = 16;
        this._errHandler.sync(this);
        switch(this._input.LA(1)) {
        case PropositionalParser.NOT:
            localctx = new NotExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;

            this.state = 7;
            this.match(PropositionalParser.NOT);
            this.state = 8;
            this.expression(9);
            break;
        case PropositionalParser.LITERAL:
            localctx = new LiteralExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 9;
            this.match(PropositionalParser.LITERAL);
            break;
        case PropositionalParser.TRUE:
            localctx = new TrueExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 10;
            this.match(PropositionalParser.TRUE);
            break;
        case PropositionalParser.FALSE:
            localctx = new FalseExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 11;
            this.match(PropositionalParser.FALSE);
            break;
        case PropositionalParser.BRACKET_OPEN:
            localctx = new ParenthesesExpContext(this, localctx);
            this._ctx = localctx;
            _prevctx = localctx;
            this.state = 12;
            this.match(PropositionalParser.BRACKET_OPEN);
            this.state = 13;
            this.expression(0);
            this.state = 14;
            this.match(PropositionalParser.BRACKET_CLOSE);
            break;
        default:
            throw new antlr4.error.NoViableAltException(this);
        }
        this._ctx.stop = this._input.LT(-1);
        this.state = 32;
        this._errHandler.sync(this);
        var _alt = this._interp.adaptivePredict(this._input,2,this._ctx)
        while(_alt!=2 && _alt!=antlr4.atn.ATN.INVALID_ALT_NUMBER) {
            if(_alt===1) {
                if(this._parseListeners!==null) {
                    this.triggerExitRuleEvent();
                }
                _prevctx = localctx;
                this.state = 30;
                this._errHandler.sync(this);
                var la_ = this._interp.adaptivePredict(this._input,1,this._ctx);
                switch(la_) {
                case 1:
                    localctx = new AndExpContext(this, new ExpressionContext(this, _parentctx, _parentState));
                    this.pushNewRecursionContext(localctx, _startState, PropositionalParser.RULE_expression);
                    this.state = 18;
                    if (!( this.precpred(this._ctx, 8))) {
                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 8)");
                    }
                    this.state = 19;
                    this.match(PropositionalParser.AND);
                    this.state = 20;
                    this.expression(9);
                    break;

                case 2:
                    localctx = new OrExpContext(this, new ExpressionContext(this, _parentctx, _parentState));
                    this.pushNewRecursionContext(localctx, _startState, PropositionalParser.RULE_expression);
                    this.state = 21;
                    if (!( this.precpred(this._ctx, 7))) {
                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 7)");
                    }
                    this.state = 22;
                    this.match(PropositionalParser.OR);
                    this.state = 23;
                    this.expression(8);
                    break;

                case 3:
                    localctx = new ImpliesExpContext(this, new ExpressionContext(this, _parentctx, _parentState));
                    this.pushNewRecursionContext(localctx, _startState, PropositionalParser.RULE_expression);
                    this.state = 24;
                    if (!( this.precpred(this._ctx, 6))) {
                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 6)");
                    }
                    this.state = 25;
                    this.match(PropositionalParser.IMPLIES);
                    this.state = 26;
                    this.expression(7);
                    break;

                case 4:
                    localctx = new IffExpContext(this, new ExpressionContext(this, _parentctx, _parentState));
                    this.pushNewRecursionContext(localctx, _startState, PropositionalParser.RULE_expression);
                    this.state = 27;
                    if (!( this.precpred(this._ctx, 5))) {
                        throw new antlr4.error.FailedPredicateException(this, "this.precpred(this._ctx, 5)");
                    }
                    this.state = 28;
                    this.match(PropositionalParser.IFF);
                    this.state = 29;
                    this.expression(6);
                    break;

                } 
            }
            this.state = 34;
            this._errHandler.sync(this);
            _alt = this._interp.adaptivePredict(this._input,2,this._ctx);
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
			return this.precpred(this._ctx, 8);
		case 1:
			return this.precpred(this._ctx, 7);
		case 2:
			return this.precpred(this._ctx, 6);
		case 3:
			return this.precpred(this._ctx, 5);
		default:
			throw "No predicate with index:" + predIndex;
	}
};


exports.PropositionalParser = PropositionalParser;
