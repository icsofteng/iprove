// Generated from src/parser/Propositional.g4 by ANTLR 4.7.1
// jshint ignore: start
var antlr4 = require('antlr4/index');


var serializedATN = ["\u0003\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964",
    "\u0002\u0013o\b\u0001\u0004\u0002\t\u0002\u0004\u0003\t\u0003\u0004",
    "\u0004\t\u0004\u0004\u0005\t\u0005\u0004\u0006\t\u0006\u0004\u0007\t",
    "\u0007\u0004\b\t\b\u0004\t\t\t\u0004\n\t\n\u0004\u000b\t\u000b\u0004",
    "\f\t\f\u0004\r\t\r\u0004\u000e\t\u000e\u0004\u000f\t\u000f\u0004\u0010",
    "\t\u0010\u0004\u0011\t\u0011\u0004\u0012\t\u0012\u0003\u0002\u0003\u0002",
    "\u0003\u0002\u0003\u0002\u0003\u0002\u0003\u0002\u0003\u0002\u0003\u0003",
    "\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003",
    "\u0003\u0004\u0003\u0004\u0003\u0004\u0003\u0004\u0003\u0005\u0003\u0005",
    "\u0003\u0005\u0003\u0005\u0003\u0006\u0003\u0006\u0003\u0006\u0003\u0007",
    "\u0003\u0007\u0003\u0007\u0003\u0007\u0003\u0007\u0003\u0007\u0003\u0007",
    "\u0003\u0007\u0003\b\u0003\b\u0003\b\u0003\b\u0003\t\u0003\t\u0003\t",
    "\u0003\t\u0003\t\u0003\n\u0003\n\u0003\n\u0003\n\u0003\n\u0003\n\u0003",
    "\u000b\u0003\u000b\u0003\f\u0003\f\u0003\r\u0003\r\u0003\u000e\u0003",
    "\u000e\u0003\u000f\u0003\u000f\u0006\u000f`\n\u000f\r\u000f\u000e\u000f",
    "a\u0003\u0010\u0003\u0010\u0006\u0010f\n\u0010\r\u0010\u000e\u0010g",
    "\u0003\u0011\u0003\u0011\u0003\u0012\u0003\u0012\u0003\u0012\u0003\u0012",
    "\u0002\u0002\u0013\u0003\u0003\u0005\u0004\u0007\u0005\t\u0006\u000b",
    "\u0007\r\b\u000f\t\u0011\n\u0013\u000b\u0015\f\u0017\r\u0019\u000e\u001b",
    "\u000f\u001d\u0010\u001f\u0011!\u0012#\u0013\u0003\u0002\u0006\u0003",
    "\u0002C\\\u0003\u0002c|\u0005\u0002C\\aac|\u0005\u0002\u000b\f\u000f",
    "\u000f\"\"\u0002p\u0002\u0003\u0003\u0002\u0002\u0002\u0002\u0005\u0003",
    "\u0002\u0002\u0002\u0002\u0007\u0003\u0002\u0002\u0002\u0002\t\u0003",
    "\u0002\u0002\u0002\u0002\u000b\u0003\u0002\u0002\u0002\u0002\r\u0003",
    "\u0002\u0002\u0002\u0002\u000f\u0003\u0002\u0002\u0002\u0002\u0011\u0003",
    "\u0002\u0002\u0002\u0002\u0013\u0003\u0002\u0002\u0002\u0002\u0015\u0003",
    "\u0002\u0002\u0002\u0002\u0017\u0003\u0002\u0002\u0002\u0002\u0019\u0003",
    "\u0002\u0002\u0002\u0002\u001b\u0003\u0002\u0002\u0002\u0002\u001d\u0003",
    "\u0002\u0002\u0002\u0002\u001f\u0003\u0002\u0002\u0002\u0002!\u0003",
    "\u0002\u0002\u0002\u0002#\u0003\u0002\u0002\u0002\u0003%\u0003\u0002",
    "\u0002\u0002\u0005,\u0003\u0002\u0002\u0002\u00073\u0003\u0002\u0002",
    "\u0002\t7\u0003\u0002\u0002\u0002\u000b;\u0003\u0002\u0002\u0002\r>",
    "\u0003\u0002\u0002\u0002\u000fF\u0003\u0002\u0002\u0002\u0011J\u0003",
    "\u0002\u0002\u0002\u0013O\u0003\u0002\u0002\u0002\u0015U\u0003\u0002",
    "\u0002\u0002\u0017W\u0003\u0002\u0002\u0002\u0019Y\u0003\u0002\u0002",
    "\u0002\u001b[\u0003\u0002\u0002\u0002\u001d]\u0003\u0002\u0002\u0002",
    "\u001fc\u0003\u0002\u0002\u0002!i\u0003\u0002\u0002\u0002#k\u0003\u0002",
    "\u0002\u0002%&\u0007h\u0002\u0002&\'\u0007q\u0002\u0002\'(\u0007t\u0002",
    "\u0002()\u0007c\u0002\u0002)*\u0007n\u0002\u0002*+\u0007n\u0002\u0002",
    "+\u0004\u0003\u0002\u0002\u0002,-\u0007g\u0002\u0002-.\u0007z\u0002",
    "\u0002./\u0007k\u0002\u0002/0\u0007u\u0002\u000201\u0007v\u0002\u0002",
    "12\u0007u\u0002\u00022\u0006\u0003\u0002\u0002\u000234\u0007p\u0002",
    "\u000245\u0007q\u0002\u000256\u0007v\u0002\u00026\b\u0003\u0002\u0002",
    "\u000278\u0007c\u0002\u000289\u0007p\u0002\u00029:\u0007f\u0002\u0002",
    ":\n\u0003\u0002\u0002\u0002;<\u0007q\u0002\u0002<=\u0007t\u0002\u0002",
    "=\f\u0003\u0002\u0002\u0002>?\u0007k\u0002\u0002?@\u0007o\u0002\u0002",
    "@A\u0007r\u0002\u0002AB\u0007n\u0002\u0002BC\u0007k\u0002\u0002CD\u0007",
    "g\u0002\u0002DE\u0007u\u0002\u0002E\u000e\u0003\u0002\u0002\u0002FG",
    "\u0007k\u0002\u0002GH\u0007h\u0002\u0002HI\u0007h\u0002\u0002I\u0010",
    "\u0003\u0002\u0002\u0002JK\u0007v\u0002\u0002KL\u0007t\u0002\u0002L",
    "M\u0007w\u0002\u0002MN\u0007g\u0002\u0002N\u0012\u0003\u0002\u0002\u0002",
    "OP\u0007h\u0002\u0002PQ\u0007c\u0002\u0002QR\u0007n\u0002\u0002RS\u0007",
    "u\u0002\u0002ST\u0007g\u0002\u0002T\u0014\u0003\u0002\u0002\u0002UV",
    "\u0007*\u0002\u0002V\u0016\u0003\u0002\u0002\u0002WX\u0007+\u0002\u0002",
    "X\u0018\u0003\u0002\u0002\u0002YZ\t\u0002\u0002\u0002Z\u001a\u0003\u0002",
    "\u0002\u0002[\\\t\u0003\u0002\u0002\\\u001c\u0003\u0002\u0002\u0002",
    "]_\t\u0002\u0002\u0002^`\t\u0003\u0002\u0002_^\u0003\u0002\u0002\u0002",
    "`a\u0003\u0002\u0002\u0002a_\u0003\u0002\u0002\u0002ab\u0003\u0002\u0002",
    "\u0002b\u001e\u0003\u0002\u0002\u0002ce\t\u0003\u0002\u0002df\t\u0004",
    "\u0002\u0002ed\u0003\u0002\u0002\u0002fg\u0003\u0002\u0002\u0002ge\u0003",
    "\u0002\u0002\u0002gh\u0003\u0002\u0002\u0002h \u0003\u0002\u0002\u0002",
    "ij\u0007.\u0002\u0002j\"\u0003\u0002\u0002\u0002kl\t\u0005\u0002\u0002",
    "lm\u0003\u0002\u0002\u0002mn\b\u0012\u0002\u0002n$\u0003\u0002\u0002",
    "\u0002\u0005\u0002ag\u0003\b\u0002\u0002"].join("");


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
PropositionalLexer.FORALL = 1;
PropositionalLexer.EXISTS = 2;
PropositionalLexer.NOT = 3;
PropositionalLexer.AND = 4;
PropositionalLexer.OR = 5;
PropositionalLexer.IMPLIES = 6;
PropositionalLexer.IFF = 7;
PropositionalLexer.TRUE = 8;
PropositionalLexer.FALSE = 9;
PropositionalLexer.BRACKET_OPEN = 10;
PropositionalLexer.BRACKET_CLOSE = 11;
PropositionalLexer.LITERAL = 12;
PropositionalLexer.VARIABLE = 13;
PropositionalLexer.CONSTANT = 14;
PropositionalLexer.NAME = 15;
PropositionalLexer.COMMA = 16;
PropositionalLexer.WS = 17;

PropositionalLexer.prototype.channelNames = [ "DEFAULT_TOKEN_CHANNEL", "HIDDEN" ];

PropositionalLexer.prototype.modeNames = [ "DEFAULT_MODE" ];

PropositionalLexer.prototype.literalNames = [ null, "'forall'", "'exists'", 
                                              "'not'", "'and'", "'or'", 
                                              "'implies'", "'iff'", "'true'", 
                                              "'false'", "'('", "')'", null, 
                                              null, null, null, "','" ];

PropositionalLexer.prototype.symbolicNames = [ null, "FORALL", "EXISTS", 
                                               "NOT", "AND", "OR", "IMPLIES", 
                                               "IFF", "TRUE", "FALSE", "BRACKET_OPEN", 
                                               "BRACKET_CLOSE", "LITERAL", 
                                               "VARIABLE", "CONSTANT", "NAME", 
                                               "COMMA", "WS" ];

PropositionalLexer.prototype.ruleNames = [ "FORALL", "EXISTS", "NOT", "AND", 
                                           "OR", "IMPLIES", "IFF", "TRUE", 
                                           "FALSE", "BRACKET_OPEN", "BRACKET_CLOSE", 
                                           "LITERAL", "VARIABLE", "CONSTANT", 
                                           "NAME", "COMMA", "WS" ];

PropositionalLexer.prototype.grammarFileName = "Propositional.g4";



exports.PropositionalLexer = PropositionalLexer;

