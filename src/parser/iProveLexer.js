// Generated from src/parser/iProve.g4 by ANTLR 4.7.1
// jshint ignore: start
var antlr4 = require('antlr4/index');


var serializedATN = ["\u0003\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964",
    "\u0002\u0018\u008c\b\u0001\u0004\u0002\t\u0002\u0004\u0003\t\u0003\u0004",
    "\u0004\t\u0004\u0004\u0005\t\u0005\u0004\u0006\t\u0006\u0004\u0007\t",
    "\u0007\u0004\b\t\b\u0004\t\t\t\u0004\n\t\n\u0004\u000b\t\u000b\u0004",
    "\f\t\f\u0004\r\t\r\u0004\u000e\t\u000e\u0004\u000f\t\u000f\u0004\u0010",
    "\t\u0010\u0004\u0011\t\u0011\u0004\u0012\t\u0012\u0004\u0013\t\u0013",
    "\u0004\u0014\t\u0014\u0004\u0015\t\u0015\u0004\u0016\t\u0016\u0004\u0017",
    "\t\u0017\u0003\u0002\u0003\u0002\u0003\u0002\u0003\u0002\u0003\u0002",
    "\u0003\u0002\u0003\u0002\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003",
    "\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0004\u0003\u0004\u0003\u0004",
    "\u0003\u0004\u0003\u0004\u0003\u0004\u0003\u0004\u0003\u0005\u0003\u0005",
    "\u0003\u0005\u0003\u0005\u0003\u0005\u0003\u0006\u0003\u0006\u0003\u0006",
    "\u0003\u0006\u0003\u0007\u0003\u0007\u0003\u0007\u0003\u0007\u0003\b",
    "\u0003\b\u0003\b\u0003\t\u0003\t\u0003\t\u0003\t\u0003\t\u0003\t\u0003",
    "\t\u0003\t\u0003\n\u0003\n\u0003\n\u0003\u000b\u0003\u000b\u0003\u000b",
    "\u0003\u000b\u0003\f\u0003\f\u0003\f\u0003\f\u0003\f\u0003\r\u0003\r",
    "\u0003\r\u0003\r\u0003\r\u0003\r\u0003\u000e\u0003\u000e\u0003\u000f",
    "\u0003\u000f\u0003\u0010\u0003\u0010\u0003\u0011\u0003\u0011\u0003\u0012",
    "\u0003\u0012\u0003\u0013\u0003\u0013\u0003\u0014\u0003\u0014\u0006\u0014",
    "}\n\u0014\r\u0014\u000e\u0014~\u0003\u0015\u0003\u0015\u0006\u0015\u0083",
    "\n\u0015\r\u0015\u000e\u0015\u0084\u0003\u0016\u0003\u0016\u0003\u0017",
    "\u0003\u0017\u0003\u0017\u0003\u0017\u0002\u0002\u0018\u0003\u0003\u0005",
    "\u0004\u0007\u0005\t\u0006\u000b\u0007\r\b\u000f\t\u0011\n\u0013\u000b",
    "\u0015\f\u0017\r\u0019\u000e\u001b\u000f\u001d\u0010\u001f\u0011!\u0012",
    "#\u0013%\u0014\'\u0015)\u0016+\u0017-\u0018\u0003\u0002\u0007\u0003",
    "\u0002C\\\u0003\u0002c|\u0004\u0002C\\c|\u0005\u0002C\\aac|\u0005\u0002",
    "\u000b\f\u000f\u000f\"\"\u0002\u008d\u0002\u0003\u0003\u0002\u0002\u0002",
    "\u0002\u0005\u0003\u0002\u0002\u0002\u0002\u0007\u0003\u0002\u0002\u0002",
    "\u0002\t\u0003\u0002\u0002\u0002\u0002\u000b\u0003\u0002\u0002\u0002",
    "\u0002\r\u0003\u0002\u0002\u0002\u0002\u000f\u0003\u0002\u0002\u0002",
    "\u0002\u0011\u0003\u0002\u0002\u0002\u0002\u0013\u0003\u0002\u0002\u0002",
    "\u0002\u0015\u0003\u0002\u0002\u0002\u0002\u0017\u0003\u0002\u0002\u0002",
    "\u0002\u0019\u0003\u0002\u0002\u0002\u0002\u001b\u0003\u0002\u0002\u0002",
    "\u0002\u001d\u0003\u0002\u0002\u0002\u0002\u001f\u0003\u0002\u0002\u0002",
    "\u0002!\u0003\u0002\u0002\u0002\u0002#\u0003\u0002\u0002\u0002\u0002",
    "%\u0003\u0002\u0002\u0002\u0002\'\u0003\u0002\u0002\u0002\u0002)\u0003",
    "\u0002\u0002\u0002\u0002+\u0003\u0002\u0002\u0002\u0002-\u0003\u0002",
    "\u0002\u0002\u0003/\u0003\u0002\u0002\u0002\u00056\u0003\u0002\u0002",
    "\u0002\u0007=\u0003\u0002\u0002\u0002\tD\u0003\u0002\u0002\u0002\u000b",
    "I\u0003\u0002\u0002\u0002\rM\u0003\u0002\u0002\u0002\u000fQ\u0003\u0002",
    "\u0002\u0002\u0011T\u0003\u0002\u0002\u0002\u0013\\\u0003\u0002\u0002",
    "\u0002\u0015_\u0003\u0002\u0002\u0002\u0017c\u0003\u0002\u0002\u0002",
    "\u0019h\u0003\u0002\u0002\u0002\u001bn\u0003\u0002\u0002\u0002\u001d",
    "p\u0003\u0002\u0002\u0002\u001fr\u0003\u0002\u0002\u0002!t\u0003\u0002",
    "\u0002\u0002#v\u0003\u0002\u0002\u0002%x\u0003\u0002\u0002\u0002\'z",
    "\u0003\u0002\u0002\u0002)\u0080\u0003\u0002\u0002\u0002+\u0086\u0003",
    "\u0002\u0002\u0002-\u0088\u0003\u0002\u0002\u0002/0\u0007c\u0002\u0002",
    "01\u0007u\u0002\u000212\u0007u\u0002\u000223\u0007w\u0002\u000234\u0007",
    "o\u0002\u000245\u0007g\u0002\u00025\u0004\u0003\u0002\u0002\u000267",
    "\u0007h\u0002\u000278\u0007q\u0002\u000289\u0007t\u0002\u00029:\u0007",
    "c\u0002\u0002:;\u0007n\u0002\u0002;<\u0007n\u0002\u0002<\u0006\u0003",
    "\u0002\u0002\u0002=>\u0007g\u0002\u0002>?\u0007z\u0002\u0002?@\u0007",
    "k\u0002\u0002@A\u0007u\u0002\u0002AB\u0007v\u0002\u0002BC\u0007u\u0002",
    "\u0002C\b\u0003\u0002\u0002\u0002DE\u0007g\u0002\u0002EF\u0007z\u0002",
    "\u0002FG\u0007k\u0002\u0002GH\u0007v\u0002\u0002H\n\u0003\u0002\u0002",
    "\u0002IJ\u0007p\u0002\u0002JK\u0007q\u0002\u0002KL\u0007v\u0002\u0002",
    "L\f\u0003\u0002\u0002\u0002MN\u0007c\u0002\u0002NO\u0007p\u0002\u0002",
    "OP\u0007f\u0002\u0002P\u000e\u0003\u0002\u0002\u0002QR\u0007q\u0002",
    "\u0002RS\u0007t\u0002\u0002S\u0010\u0003\u0002\u0002\u0002TU\u0007k",
    "\u0002\u0002UV\u0007o\u0002\u0002VW\u0007r\u0002\u0002WX\u0007n\u0002",
    "\u0002XY\u0007k\u0002\u0002YZ\u0007g\u0002\u0002Z[\u0007u\u0002\u0002",
    "[\u0012\u0003\u0002\u0002\u0002\\]\u0007?\u0002\u0002]^\u0007@\u0002",
    "\u0002^\u0014\u0003\u0002\u0002\u0002_`\u0007k\u0002\u0002`a\u0007h",
    "\u0002\u0002ab\u0007h\u0002\u0002b\u0016\u0003\u0002\u0002\u0002cd\u0007",
    "v\u0002\u0002de\u0007t\u0002\u0002ef\u0007w\u0002\u0002fg\u0007g\u0002",
    "\u0002g\u0018\u0003\u0002\u0002\u0002hi\u0007h\u0002\u0002ij\u0007c",
    "\u0002\u0002jk\u0007n\u0002\u0002kl\u0007u\u0002\u0002lm\u0007g\u0002",
    "\u0002m\u001a\u0003\u0002\u0002\u0002no\u0007*\u0002\u0002o\u001c\u0003",
    "\u0002\u0002\u0002pq\u0007+\u0002\u0002q\u001e\u0003\u0002\u0002\u0002",
    "rs\u0007]\u0002\u0002s \u0003\u0002\u0002\u0002tu\u0007_\u0002\u0002",
    "u\"\u0003\u0002\u0002\u0002vw\t\u0002\u0002\u0002w$\u0003\u0002\u0002",
    "\u0002xy\t\u0003\u0002\u0002y&\u0003\u0002\u0002\u0002z|\t\u0002\u0002",
    "\u0002{}\t\u0004\u0002\u0002|{\u0003\u0002\u0002\u0002}~\u0003\u0002",
    "\u0002\u0002~|\u0003\u0002\u0002\u0002~\u007f\u0003\u0002\u0002\u0002",
    "\u007f(\u0003\u0002\u0002\u0002\u0080\u0082\t\u0003\u0002\u0002\u0081",
    "\u0083\t\u0005\u0002\u0002\u0082\u0081\u0003\u0002\u0002\u0002\u0083",
    "\u0084\u0003\u0002\u0002\u0002\u0084\u0082\u0003\u0002\u0002\u0002\u0084",
    "\u0085\u0003\u0002\u0002\u0002\u0085*\u0003\u0002\u0002\u0002\u0086",
    "\u0087\u0007.\u0002\u0002\u0087,\u0003\u0002\u0002\u0002\u0088\u0089",
    "\t\u0006\u0002\u0002\u0089\u008a\u0003\u0002\u0002\u0002\u008a\u008b",
    "\b\u0017\u0002\u0002\u008b.\u0003\u0002\u0002\u0002\u0005\u0002~\u0084",
    "\u0003\b\u0002\u0002"].join("");


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
iProveLexer.ASSUME = 1;
iProveLexer.FORALL = 2;
iProveLexer.EXISTS = 3;
iProveLexer.EXIT = 4;
iProveLexer.NOT = 5;
iProveLexer.AND = 6;
iProveLexer.OR = 7;
iProveLexer.IMPLIES = 8;
iProveLexer.IMPLIES2 = 9;
iProveLexer.IFF = 10;
iProveLexer.TRUE = 11;
iProveLexer.FALSE = 12;
iProveLexer.BRACKET_OPEN = 13;
iProveLexer.BRACKET_CLOSE = 14;
iProveLexer.SQ_BRACKET_OPEN = 15;
iProveLexer.SQ_BRACKET_CLOSE = 16;
iProveLexer.LITERAL = 17;
iProveLexer.VARIABLE = 18;
iProveLexer.CONSTANT = 19;
iProveLexer.NAME = 20;
iProveLexer.COMMA = 21;
iProveLexer.WS = 22;

iProveLexer.prototype.channelNames = [ "DEFAULT_TOKEN_CHANNEL", "HIDDEN" ];

iProveLexer.prototype.modeNames = [ "DEFAULT_MODE" ];

iProveLexer.prototype.literalNames = [ null, "'assume'", "'forall'", "'exists'", 
                                       "'exit'", "'not'", "'and'", "'or'", 
                                       "'implies'", "'=>'", "'iff'", "'true'", 
                                       "'false'", "'('", "')'", "'['", "']'", 
                                       null, null, null, null, "','" ];

iProveLexer.prototype.symbolicNames = [ null, "ASSUME", "FORALL", "EXISTS", 
                                        "EXIT", "NOT", "AND", "OR", "IMPLIES", 
                                        "IMPLIES2", "IFF", "TRUE", "FALSE", 
                                        "BRACKET_OPEN", "BRACKET_CLOSE", 
                                        "SQ_BRACKET_OPEN", "SQ_BRACKET_CLOSE", 
                                        "LITERAL", "VARIABLE", "CONSTANT", 
                                        "NAME", "COMMA", "WS" ];

iProveLexer.prototype.ruleNames = [ "ASSUME", "FORALL", "EXISTS", "EXIT", 
                                    "NOT", "AND", "OR", "IMPLIES", "IMPLIES2", 
                                    "IFF", "TRUE", "FALSE", "BRACKET_OPEN", 
                                    "BRACKET_CLOSE", "SQ_BRACKET_OPEN", 
                                    "SQ_BRACKET_CLOSE", "LITERAL", "VARIABLE", 
                                    "CONSTANT", "NAME", "COMMA", "WS" ];

iProveLexer.prototype.grammarFileName = "iProve.g4";



exports.iProveLexer = iProveLexer;

