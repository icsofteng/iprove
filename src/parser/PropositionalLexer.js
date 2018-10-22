// Generated from src/parser/Propositional.g4 by ANTLR 4.7.1
// jshint ignore: start
var antlr4 = require('antlr4/index');


var serializedATN = ["\u0003\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964",
    "\u0002\rE\b\u0001\u0004\u0002\t\u0002\u0004\u0003\t\u0003\u0004\u0004",
    "\t\u0004\u0004\u0005\t\u0005\u0004\u0006\t\u0006\u0004\u0007\t\u0007",
    "\u0004\b\t\b\u0004\t\t\t\u0004\n\t\n\u0004\u000b\t\u000b\u0004\f\t\f",
    "\u0003\u0002\u0003\u0002\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003",
    "\u0003\u0004\u0003\u0004\u0003\u0004\u0003\u0004\u0003\u0005\u0003\u0005",
    "\u0003\u0005\u0003\u0006\u0003\u0006\u0003\u0006\u0003\u0006\u0003\u0006",
    "\u0003\u0006\u0003\u0006\u0003\u0006\u0003\u0007\u0003\u0007\u0003\u0007",
    "\u0003\u0007\u0003\b\u0003\b\u0003\b\u0003\b\u0003\b\u0003\t\u0003\t",
    "\u0003\t\u0003\t\u0003\t\u0003\t\u0003\n\u0003\n\u0003\u000b\u0003\u000b",
    "\u0003\f\u0003\f\u0003\f\u0003\f\u0002\u0002\r\u0003\u0003\u0005\u0004",
    "\u0007\u0005\t\u0006\u000b\u0007\r\b\u000f\t\u0011\n\u0013\u000b\u0015",
    "\f\u0017\r\u0003\u0002\u0004\u0003\u0002c|\u0005\u0002\u000b\f\u000f",
    "\u000f\"\"\u0002D\u0002\u0003\u0003\u0002\u0002\u0002\u0002\u0005\u0003",
    "\u0002\u0002\u0002\u0002\u0007\u0003\u0002\u0002\u0002\u0002\t\u0003",
    "\u0002\u0002\u0002\u0002\u000b\u0003\u0002\u0002\u0002\u0002\r\u0003",
    "\u0002\u0002\u0002\u0002\u000f\u0003\u0002\u0002\u0002\u0002\u0011\u0003",
    "\u0002\u0002\u0002\u0002\u0013\u0003\u0002\u0002\u0002\u0002\u0015\u0003",
    "\u0002\u0002\u0002\u0002\u0017\u0003\u0002\u0002\u0002\u0003\u0019\u0003",
    "\u0002\u0002\u0002\u0005\u001b\u0003\u0002\u0002\u0002\u0007\u001f\u0003",
    "\u0002\u0002\u0002\t#\u0003\u0002\u0002\u0002\u000b&\u0003\u0002\u0002",
    "\u0002\r.\u0003\u0002\u0002\u0002\u000f2\u0003\u0002\u0002\u0002\u0011",
    "7\u0003\u0002\u0002\u0002\u0013=\u0003\u0002\u0002\u0002\u0015?\u0003",
    "\u0002\u0002\u0002\u0017A\u0003\u0002\u0002\u0002\u0019\u001a\t\u0002",
    "\u0002\u0002\u001a\u0004\u0003\u0002\u0002\u0002\u001b\u001c\u0007p",
    "\u0002\u0002\u001c\u001d\u0007q\u0002\u0002\u001d\u001e\u0007v\u0002",
    "\u0002\u001e\u0006\u0003\u0002\u0002\u0002\u001f \u0007c\u0002\u0002",
    " !\u0007p\u0002\u0002!\"\u0007f\u0002\u0002\"\b\u0003\u0002\u0002\u0002",
    "#$\u0007q\u0002\u0002$%\u0007t\u0002\u0002%\n\u0003\u0002\u0002\u0002",
    "&\'\u0007k\u0002\u0002\'(\u0007o\u0002\u0002()\u0007r\u0002\u0002)*",
    "\u0007n\u0002\u0002*+\u0007k\u0002\u0002+,\u0007g\u0002\u0002,-\u0007",
    "u\u0002\u0002-\f\u0003\u0002\u0002\u0002./\u0007k\u0002\u0002/0\u0007",
    "h\u0002\u000201\u0007h\u0002\u00021\u000e\u0003\u0002\u0002\u000223",
    "\u0007v\u0002\u000234\u0007t\u0002\u000245\u0007w\u0002\u000256\u0007",
    "g\u0002\u00026\u0010\u0003\u0002\u0002\u000278\u0007h\u0002\u000289",
    "\u0007c\u0002\u00029:\u0007n\u0002\u0002:;\u0007u\u0002\u0002;<\u0007",
    "g\u0002\u0002<\u0012\u0003\u0002\u0002\u0002=>\u0007*\u0002\u0002>\u0014",
    "\u0003\u0002\u0002\u0002?@\u0007+\u0002\u0002@\u0016\u0003\u0002\u0002",
    "\u0002AB\t\u0003\u0002\u0002BC\u0003\u0002\u0002\u0002CD\b\f\u0002\u0002",
    "D\u0018\u0003\u0002\u0002\u0002\u0003\u0002\u0003\b\u0002\u0002"].join("");


var atn = new antlr4.atn.ATNDeserializer().deserialize(serializedATN);

var decisionsToDFA = atn.decisionToState.map( function(ds, index) { return new antlr4.dfa.DFA(ds, index); });

function PropositionalLexer(input) {
	antlr4.Lexer.call(this, input);
    this._interp = new antlr4.atn.LexerATNSimulator(this, atn, decisionsToDFA, new antlr4.PredictionContextCache());
    return this;
}

PropositionalLexer.prototype = Object.create(antlr4.Lexer.prototype);
PropositionalLexer.prototype.constructor = PropositionalLexer;

Object.defineProperty(PropositionalLexer.prototype, "atn", {
        get : function() {
                return atn;
        }
});

PropositionalLexer.EOF = antlr4.Token.EOF;
PropositionalLexer.LITERAL = 1;
PropositionalLexer.NOT = 2;
PropositionalLexer.AND = 3;
PropositionalLexer.OR = 4;
PropositionalLexer.IMPLIES = 5;
PropositionalLexer.IFF = 6;
PropositionalLexer.TRUE = 7;
PropositionalLexer.FALSE = 8;
PropositionalLexer.BRACKET_OPEN = 9;
PropositionalLexer.BRACKET_CLOSE = 10;
PropositionalLexer.WS = 11;

PropositionalLexer.prototype.channelNames = [ "DEFAULT_TOKEN_CHANNEL", "HIDDEN" ];

PropositionalLexer.prototype.modeNames = [ "DEFAULT_MODE" ];

PropositionalLexer.prototype.literalNames = [ null, null, "'not'", "'and'", 
                                              "'or'", "'implies'", "'iff'", 
                                              "'true'", "'false'", "'('", 
                                              "')'" ];

PropositionalLexer.prototype.symbolicNames = [ null, "LITERAL", "NOT", "AND", 
                                               "OR", "IMPLIES", "IFF", "TRUE", 
                                               "FALSE", "BRACKET_OPEN", 
                                               "BRACKET_CLOSE", "WS" ];

PropositionalLexer.prototype.ruleNames = [ "LITERAL", "NOT", "AND", "OR", 
                                           "IMPLIES", "IFF", "TRUE", "FALSE", 
                                           "BRACKET_OPEN", "BRACKET_CLOSE", 
                                           "WS" ];

PropositionalLexer.prototype.grammarFileName = "Propositional.g4";



exports.PropositionalLexer = PropositionalLexer;

