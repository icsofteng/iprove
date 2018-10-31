// Generated from src/parser/iProve.g4 by ANTLR 4.7.1
// jshint ignore: start
var antlr4 = require('antlr4/index');


var serializedATN = ["\u0003\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964",
    "\u0002\u0015w\b\u0001\u0004\u0002\t\u0002\u0004\u0003\t\u0003\u0004",
    "\u0004\t\u0004\u0004\u0005\t\u0005\u0004\u0006\t\u0006\u0004\u0007\t",
    "\u0007\u0004\b\t\b\u0004\t\t\t\u0004\n\t\n\u0004\u000b\t\u000b\u0004",
    "\f\t\f\u0004\r\t\r\u0004\u000e\t\u000e\u0004\u000f\t\u000f\u0004\u0010",
    "\t\u0010\u0004\u0011\t\u0011\u0004\u0012\t\u0012\u0004\u0013\t\u0013",
    "\u0004\u0014\t\u0014\u0003\u0002\u0003\u0002\u0003\u0002\u0003\u0002",
    "\u0003\u0002\u0003\u0002\u0003\u0002\u0003\u0003\u0003\u0003\u0003\u0003",
    "\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0004\u0003\u0004",
    "\u0003\u0004\u0003\u0004\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0005",
    "\u0003\u0006\u0003\u0006\u0003\u0006\u0003\u0007\u0003\u0007\u0003\u0007",
    "\u0003\u0007\u0003\u0007\u0003\u0007\u0003\u0007\u0003\u0007\u0003\b",
    "\u0003\b\u0003\b\u0003\b\u0003\t\u0003\t\u0003\t\u0003\t\u0003\t\u0003",
    "\n\u0003\n\u0003\n\u0003\n\u0003\n\u0003\n\u0003\u000b\u0003\u000b\u0003",
    "\f\u0003\f\u0003\r\u0003\r\u0003\u000e\u0003\u000e\u0003\u000f\u0003",
    "\u000f\u0003\u0010\u0003\u0010\u0003\u0011\u0003\u0011\u0006\u0011h",
    "\n\u0011\r\u0011\u000e\u0011i\u0003\u0012\u0003\u0012\u0006\u0012n\n",
    "\u0012\r\u0012\u000e\u0012o\u0003\u0013\u0003\u0013\u0003\u0014\u0003",
    "\u0014\u0003\u0014\u0003\u0014\u0002\u0002\u0015\u0003\u0003\u0005\u0004",
    "\u0007\u0005\t\u0006\u000b\u0007\r\b\u000f\t\u0011\n\u0013\u000b\u0015",
    "\f\u0017\r\u0019\u000e\u001b\u000f\u001d\u0010\u001f\u0011!\u0012#\u0013",
    "%\u0014\'\u0015\u0003\u0002\u0007\u0003\u0002C\\\u0003\u0002c|\u0004",
    "\u0002C\\c|\u0005\u0002C\\aac|\u0005\u0002\u000b\f\u000f\u000f\"\"\u0002",
    "x\u0002\u0003\u0003\u0002\u0002\u0002\u0002\u0005\u0003\u0002\u0002",
    "\u0002\u0002\u0007\u0003\u0002\u0002\u0002\u0002\t\u0003\u0002\u0002",
    "\u0002\u0002\u000b\u0003\u0002\u0002\u0002\u0002\r\u0003\u0002\u0002",
    "\u0002\u0002\u000f\u0003\u0002\u0002\u0002\u0002\u0011\u0003\u0002\u0002",
    "\u0002\u0002\u0013\u0003\u0002\u0002\u0002\u0002\u0015\u0003\u0002\u0002",
    "\u0002\u0002\u0017\u0003\u0002\u0002\u0002\u0002\u0019\u0003\u0002\u0002",
    "\u0002\u0002\u001b\u0003\u0002\u0002\u0002\u0002\u001d\u0003\u0002\u0002",
    "\u0002\u0002\u001f\u0003\u0002\u0002\u0002\u0002!\u0003\u0002\u0002",
    "\u0002\u0002#\u0003\u0002\u0002\u0002\u0002%\u0003\u0002\u0002\u0002",
    "\u0002\'\u0003\u0002\u0002\u0002\u0003)\u0003\u0002\u0002\u0002\u0005",
    "0\u0003\u0002\u0002\u0002\u00077\u0003\u0002\u0002\u0002\t;\u0003\u0002",
    "\u0002\u0002\u000b?\u0003\u0002\u0002\u0002\rB\u0003\u0002\u0002\u0002",
    "\u000fJ\u0003\u0002\u0002\u0002\u0011N\u0003\u0002\u0002\u0002\u0013",
    "S\u0003\u0002\u0002\u0002\u0015Y\u0003\u0002\u0002\u0002\u0017[\u0003",
    "\u0002\u0002\u0002\u0019]\u0003\u0002\u0002\u0002\u001b_\u0003\u0002",
    "\u0002\u0002\u001da\u0003\u0002\u0002\u0002\u001fc\u0003\u0002\u0002",
    "\u0002!e\u0003\u0002\u0002\u0002#k\u0003\u0002\u0002\u0002%q\u0003\u0002",
    "\u0002\u0002\'s\u0003\u0002\u0002\u0002)*\u0007h\u0002\u0002*+\u0007",
    "q\u0002\u0002+,\u0007t\u0002\u0002,-\u0007c\u0002\u0002-.\u0007n\u0002",
    "\u0002./\u0007n\u0002\u0002/\u0004\u0003\u0002\u0002\u000201\u0007g",
    "\u0002\u000212\u0007z\u0002\u000223\u0007k\u0002\u000234\u0007u\u0002",
    "\u000245\u0007v\u0002\u000256\u0007u\u0002\u00026\u0006\u0003\u0002",
    "\u0002\u000278\u0007p\u0002\u000289\u0007q\u0002\u00029:\u0007v\u0002",
    "\u0002:\b\u0003\u0002\u0002\u0002;<\u0007c\u0002\u0002<=\u0007p\u0002",
    "\u0002=>\u0007f\u0002\u0002>\n\u0003\u0002\u0002\u0002?@\u0007q\u0002",
    "\u0002@A\u0007t\u0002\u0002A\f\u0003\u0002\u0002\u0002BC\u0007k\u0002",
    "\u0002CD\u0007o\u0002\u0002DE\u0007r\u0002\u0002EF\u0007n\u0002\u0002",
    "FG\u0007k\u0002\u0002GH\u0007g\u0002\u0002HI\u0007u\u0002\u0002I\u000e",
    "\u0003\u0002\u0002\u0002JK\u0007k\u0002\u0002KL\u0007h\u0002\u0002L",
    "M\u0007h\u0002\u0002M\u0010\u0003\u0002\u0002\u0002NO\u0007v\u0002\u0002",
    "OP\u0007t\u0002\u0002PQ\u0007w\u0002\u0002QR\u0007g\u0002\u0002R\u0012",
    "\u0003\u0002\u0002\u0002ST\u0007h\u0002\u0002TU\u0007c\u0002\u0002U",
    "V\u0007n\u0002\u0002VW\u0007u\u0002\u0002WX\u0007g\u0002\u0002X\u0014",
    "\u0003\u0002\u0002\u0002YZ\u0007*\u0002\u0002Z\u0016\u0003\u0002\u0002",
    "\u0002[\\\u0007+\u0002\u0002\\\u0018\u0003\u0002\u0002\u0002]^\u0007",
    "]\u0002\u0002^\u001a\u0003\u0002\u0002\u0002_`\u0007_\u0002\u0002`\u001c",
    "\u0003\u0002\u0002\u0002ab\t\u0002\u0002\u0002b\u001e\u0003\u0002\u0002",
    "\u0002cd\t\u0003\u0002\u0002d \u0003\u0002\u0002\u0002eg\t\u0002\u0002",
    "\u0002fh\t\u0004\u0002\u0002gf\u0003\u0002\u0002\u0002hi\u0003\u0002",
    "\u0002\u0002ig\u0003\u0002\u0002\u0002ij\u0003\u0002\u0002\u0002j\"",
    "\u0003\u0002\u0002\u0002km\t\u0003\u0002\u0002ln\t\u0005\u0002\u0002",
    "ml\u0003\u0002\u0002\u0002no\u0003\u0002\u0002\u0002om\u0003\u0002\u0002",
    "\u0002op\u0003\u0002\u0002\u0002p$\u0003\u0002\u0002\u0002qr\u0007.",
    "\u0002\u0002r&\u0003\u0002\u0002\u0002st\t\u0006\u0002\u0002tu\u0003",
    "\u0002\u0002\u0002uv\b\u0014\u0002\u0002v(\u0003\u0002\u0002\u0002\u0005",
    "\u0002io\u0003\b\u0002\u0002"].join("");


var atn = new antlr4.atn.ATNDeserializer().deserialize(serializedATN);

var decisionsToDFA = atn.decisionToState.map( function(ds, index) { return new antlr4.dfa.DFA(ds, index); });

function iProveLexer(input) {
	antlr4.Lexer.call(this, input);
    this._interp = new antlr4.atn.LexerATNSimulator(this, atn, decisionsToDFA, new antlr4.PredictionContextCache());
    return this;
}

iProveLexer.prototype = Object.create(antlr4.Lexer.prototype);
iProveLexer.prototype.constructor = iProveLexer;

Object.defineProperty(iProveLexer.prototype, "atn", {
        get : function() {
                return atn;
        }
});

iProveLexer.EOF = antlr4.Token.EOF;
iProveLexer.FORALL = 1;
iProveLexer.EXISTS = 2;
iProveLexer.NOT = 3;
iProveLexer.AND = 4;
iProveLexer.OR = 5;
iProveLexer.IMPLIES = 6;
iProveLexer.IFF = 7;
iProveLexer.TRUE = 8;
iProveLexer.FALSE = 9;
iProveLexer.BRACKET_OPEN = 10;
iProveLexer.BRACKET_CLOSE = 11;
iProveLexer.SQ_BRACKET_OPEN = 12;
iProveLexer.SQ_BRACKET_CLOSE = 13;
iProveLexer.LITERAL = 14;
iProveLexer.VARIABLE = 15;
iProveLexer.CONSTANT = 16;
iProveLexer.NAME = 17;
iProveLexer.COMMA = 18;
iProveLexer.WS = 19;

iProveLexer.prototype.channelNames = [ "DEFAULT_TOKEN_CHANNEL", "HIDDEN" ];

iProveLexer.prototype.modeNames = [ "DEFAULT_MODE" ];

iProveLexer.prototype.literalNames = [ null, "'forall'", "'exists'", "'not'", 
                                       "'and'", "'or'", "'implies'", "'iff'", 
                                       "'true'", "'false'", "'('", "')'", 
                                       "'['", "']'", null, null, null, null, 
                                       "','" ];

iProveLexer.prototype.symbolicNames = [ null, "FORALL", "EXISTS", "NOT", 
                                        "AND", "OR", "IMPLIES", "IFF", "TRUE", 
                                        "FALSE", "BRACKET_OPEN", "BRACKET_CLOSE", 
                                        "SQ_BRACKET_OPEN", "SQ_BRACKET_CLOSE", 
                                        "LITERAL", "VARIABLE", "CONSTANT", 
                                        "NAME", "COMMA", "WS" ];

iProveLexer.prototype.ruleNames = [ "FORALL", "EXISTS", "NOT", "AND", "OR", 
                                    "IMPLIES", "IFF", "TRUE", "FALSE", "BRACKET_OPEN", 
                                    "BRACKET_CLOSE", "SQ_BRACKET_OPEN", 
                                    "SQ_BRACKET_CLOSE", "LITERAL", "VARIABLE", 
                                    "CONSTANT", "NAME", "COMMA", "WS" ];

iProveLexer.prototype.grammarFileName = "iProve.g4";



exports.iProveLexer = iProveLexer;

